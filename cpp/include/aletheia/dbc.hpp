// SPDX-License-Identifier: BSD-2-Clause
#pragma once

// DbcSignal/DbcMessage embed vocabulary types (SignalName, CanId, Dlc,
// NodeName, BitPosition, BitLength, ByteOrder, RationalFactor, ...), so
// callers that include dbc.hpp always need those symbols as well.
#include <aletheia/types.hpp> // IWYU pragma: export

#include <cstddef>
#include <cstdint>
#include <functional>
#include <optional>
#include <string>
#include <unordered_map>
#include <utility>
#include <variant>
#include <vector>

namespace aletheia {

// ---------------------------------------------------------------------------
// Lazy mutable index — encapsulates the cache behind a private optional map.
// Public interface is const-safe: ensure() populates once, find() reads.
// ---------------------------------------------------------------------------

namespace detail {

template<typename Key, typename Hash = std::hash<Key>>
class LazyIndex {
public:
    /// Populate the index once via a builder callback: void(map&).
    template<typename Builder>
    void ensure(Builder&& build) const {
        if (cache_)
            return;
        cache_.emplace();
        std::forward<Builder>(build)(*cache_);
    }

    /// Look up a key; returns std::nullopt if absent or not yet built.
    [[nodiscard]] auto find(const Key& key) const -> std::optional<std::size_t> {
        if (!cache_)
            return std::nullopt;
        auto it = cache_->find(key);
        return (it != cache_->end()) ? std::optional{it->second} : std::nullopt;
    }

private:
    mutable std::optional<std::unordered_map<Key, std::size_t, Hash>> cache_;
};

} // namespace detail

// ---------------------------------------------------------------------------
// Signal presence (always vs multiplexed)
// ---------------------------------------------------------------------------

struct AlwaysPresent {};

struct Multiplexed {
    SignalName multiplexor;
    std::vector<MultiplexValue> mux_values;
};

using SignalPresence = std::variant<AlwaysPresent, Multiplexed>;

// ---------------------------------------------------------------------------
// DBC signal definition
// ---------------------------------------------------------------------------

struct DbcSignal {
    SignalName name;
    BitPosition start_bit;
    BitLength bit_length;
    ByteOrder byte_order;
    bool is_signed;
    RationalFactor factor;
    RationalOffset offset;
    RationalBound minimum;
    RationalBound maximum;
    Unit unit;
    SignalPresence presence;
    std::vector<std::string> receivers;
};

// ---------------------------------------------------------------------------
// DBC message definition
// ---------------------------------------------------------------------------

struct DbcMessage {
    CanId id;
    MessageName name;
    Dlc dlc;
    NodeName sender;
    // Additional transmitters declared on BO_TX_BU_ lines. The BO_ primary
    // stays in `sender`; these are the extras the Agda validator binds
    // against the BU_ node table via UnknownMessageSender.
    std::vector<std::string> senders;
    std::vector<DbcSignal> signals;

    // --- Multiplexing query helpers (defined in dbc.cpp) ---

    [[nodiscard]] auto is_multiplexed() const -> bool;
    [[nodiscard]] auto always_present_signals() const -> std::vector<DbcSignal>;
    [[nodiscard]] auto multiplexed_signals() const -> std::vector<DbcSignal>;
    [[nodiscard]] auto multiplexor_names() const -> std::vector<SignalName>;
    [[nodiscard]] auto mux_values(const SignalName& multiplexor) const
        -> std::vector<MultiplexValue>;
    [[nodiscard]] auto signals_for_mux_value(const SignalName& multiplexor,
                                             MultiplexValue value) const -> std::vector<DbcSignal>;
    [[nodiscard]] auto signal_by_name(const SignalName& name) const -> const DbcSignal*;

    // Lazily populated by signal_by_name(). Mutable so const methods can
    // populate the cache on first access. Public because DbcDefinition
    // holds DbcMessage by value, so downstream aggregate construction works.
    mutable detail::LazyIndex<std::string> signal_index_cache;
};

// ---------------------------------------------------------------------------
// DBC signal group (``SIG_GROUP_`` keyword)
//
// The DBC spec carries a parent-message id and a repetition count on the
// wire; the Agda core only models the flattened ``{name, signals}`` view
// because signal-name uniqueness is enforced globally by the validator,
// so reconstructing message context on format_dbc is unnecessary.
// ---------------------------------------------------------------------------

struct DbcSignalGroup {
    std::string name;
    std::vector<SignalName> signals;
};

// ---------------------------------------------------------------------------
// DBC environment variable (``EV_`` keyword)
//
// The DBC spec encodes int/float/string as 0/1/2 respectively on the wire;
// the Agda core preserves that vocabulary directly (``varTypeToℕ``).
// ---------------------------------------------------------------------------

enum class DbcVarType : int {
    Int = 0,
    Float = 1,
    String = 2,
};

struct DbcEnvironmentVar {
    std::string name;
    DbcVarType var_type;
    // Exact rationals — cantools exposes these as int-or-float depending on
    // var_type; Python uses ``Fraction``, C++ uses ``Rational`` to preserve
    // decimal intent through the wire round-trip.
    Rational initial;
    Rational minimum;
    Rational maximum;
};

// ---------------------------------------------------------------------------
// DBC value table (``VAL_TABLE_`` keyword)
// ---------------------------------------------------------------------------

struct DbcValueEntry {
    std::int64_t value;
    std::string description;
};

struct DbcValueTable {
    std::string name;
    std::vector<DbcValueEntry> entries;
};

// ---------------------------------------------------------------------------
// Tier 2 DBC metadata: nodes (BU_), comments (CM_), attributes (BA_*)
//
// The wire format uses ``"kind"`` as a discriminator on every tagged union
// so Agda's parseAttribute/parseCommentTarget/... can dispatch without
// peeking at the rest of the object. Each C++ variant alternative mirrors
// one Agda constructor; fields after ``kind`` are laid out in the same
// order Agda's formatter emits.
// ---------------------------------------------------------------------------

struct DbcNode {
    std::string name;
};

// ---- Comment targets (CM_ family) ----

struct DbcCommentTargetNetwork {};
struct DbcCommentTargetNode {
    std::string node;
};
// Extended flag is emitted on the wire only when true (Agda's formatCANId
// omits "extended" for 11-bit IDs). Default-false here keeps round-trip
// byte-identical for the common standard-ID case.
struct DbcCommentTargetMessage {
    std::uint32_t id = 0;
    bool extended = false;
};
struct DbcCommentTargetSignal {
    std::uint32_t id = 0;
    bool extended = false;
    std::string signal;
};
struct DbcCommentTargetEnvVar {
    std::string env_var;
};

using DbcCommentTarget =
    std::variant<DbcCommentTargetNetwork, DbcCommentTargetNode, DbcCommentTargetMessage,
                 DbcCommentTargetSignal, DbcCommentTargetEnvVar>;

struct DbcComment {
    DbcCommentTarget target;
    std::string text;
};

// ---- Attribute scope (BA_DEF_ keyword class) ----

enum class DbcAttrScope {
    Network,
    Node,
    Message,
    Signal,
    EnvVar,
    NodeMsg,
    NodeSig,
};

// ---- Attribute types (RHS of BA_DEF_) ----

struct DbcAttrTypeInt {
    std::int64_t min = 0;
    std::int64_t max = 0;
};
// Float bounds use exact Rational (matching Python's Fraction) rather than
// double — ATFloat carries ℚ in the Agda core, and lossy conversion would
// break round-trip parity with the Python binding.
struct DbcAttrTypeFloat {
    Rational min;
    Rational max;
};
struct DbcAttrTypeString {};
struct DbcAttrTypeEnum {
    std::vector<std::string> values;
};
struct DbcAttrTypeHex {
    std::int64_t min = 0;
    std::int64_t max = 0;
};

using DbcAttrType = std::variant<DbcAttrTypeInt, DbcAttrTypeFloat, DbcAttrTypeString,
                                 DbcAttrTypeEnum, DbcAttrTypeHex>;

// ---- Attribute values (BA_, BA_REL_, BA_DEF_DEF_) ----

struct DbcAttrValueInt {
    std::int64_t value = 0;
};
// Same Rational-over-double rationale as DbcAttrTypeFloat above.
struct DbcAttrValueFloat {
    Rational value;
};
struct DbcAttrValueString {
    std::string value;
};
// Enum value is a ℕ index into the corresponding DbcAttrTypeEnum::values list.
struct DbcAttrValueEnum {
    std::int64_t value = 0;
};
struct DbcAttrValueHex {
    std::int64_t value = 0;
};

using DbcAttrValue = std::variant<DbcAttrValueInt, DbcAttrValueFloat, DbcAttrValueString,
                                  DbcAttrValueEnum, DbcAttrValueHex>;

// ---- Attribute assignment targets (LHS of BA_ / BA_REL_) ----

struct DbcAttrTargetNetwork {};
struct DbcAttrTargetNode {
    std::string node;
};
struct DbcAttrTargetMessage {
    std::uint32_t id = 0;
    bool extended = false;
};
struct DbcAttrTargetSignal {
    std::uint32_t id = 0;
    bool extended = false;
    std::string signal;
};
struct DbcAttrTargetEnvVar {
    std::string env_var;
};
struct DbcAttrTargetNodeMsg {
    std::string node;
    std::uint32_t id = 0;
    bool extended = false;
};
struct DbcAttrTargetNodeSig {
    std::string node;
    std::uint32_t id = 0;
    bool extended = false;
    std::string signal;
};

using DbcAttrTarget =
    std::variant<DbcAttrTargetNetwork, DbcAttrTargetNode, DbcAttrTargetMessage, DbcAttrTargetSignal,
                 DbcAttrTargetEnvVar, DbcAttrTargetNodeMsg, DbcAttrTargetNodeSig>;

// ---- Attribute ADT (3 variants: BA_DEF_ / BA_DEF_DEF_ / BA_) ----

struct DbcAttrDef {
    std::string name;
    DbcAttrScope scope;
    DbcAttrType attr_type;
};
struct DbcAttrDefault {
    std::string name;
    DbcAttrValue value;
};
struct DbcAttrAssign {
    std::string name;
    DbcAttrTarget target;
    DbcAttrValue value;
};

using DbcAttribute = std::variant<DbcAttrDef, DbcAttrDefault, DbcAttrAssign>;

// ---------------------------------------------------------------------------
// Complete DBC definition
//
// There are three supported ways to obtain a DbcDefinition:
//   1. Construct it programmatically (messages/signals as aggregate init).
//   2. `load_dbc_from_excel()` from <aletheia/excel.hpp> — reads the
//      project-native Excel layout.
//   3. Hand-deserialize from JSON — the wire format used by the Python
//      binding and by the Agda core.
//
// There is intentionally no `.dbc` text-file parser in the C++ binding.
// Users with legacy `.dbc` files should run them through the cantools
// Python CLI once to produce a JSON DBC, then load that JSON from C++.
// See docs/architecture/INTERFACES.md ("DBC text workaround") and
// memory item `project_binding_feature_gaps.md` — a native `.dbc` text
// parser is tracked as a Phase 6 feature request.
// ---------------------------------------------------------------------------

struct DbcDefinition {
    std::string version; // plain string (not a domain identifier)
    std::vector<DbcMessage> messages;
    // Tier 1 DBC metadata (Agda ``DBC`` record fields 3-5). Absent on the
    // wire equals empty here — format_dbc always emits all three arrays
    // even when they are empty.
    std::vector<DbcSignalGroup> signal_groups;
    std::vector<DbcEnvironmentVar> environment_vars;
    std::vector<DbcValueTable> value_tables;
    // Tier 2 DBC metadata (Agda ``DBC`` record fields 6-8).
    std::vector<DbcNode> nodes;
    std::vector<DbcComment> comments;
    std::vector<DbcAttribute> attributes;

    // --- Lookup helpers (defined in dbc.cpp) ---

    [[nodiscard]] auto message_by_id(const CanId& id) const -> const DbcMessage*;
    [[nodiscard]] auto message_by_name(const MessageName& name) const -> const DbcMessage*;

    // Implementation detail — lazily populated by message_by_id/name().
    mutable detail::LazyIndex<std::string> name_index_cache;
    mutable detail::LazyIndex<std::uint64_t> id_index_cache;
};

} // namespace aletheia
