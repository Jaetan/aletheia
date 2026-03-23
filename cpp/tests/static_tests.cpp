// Layer 1: Compile-time tests.
// If this file compiles, all static assertions pass. No runtime needed.

#include <aletheia/aletheia.hpp>

#include <concepts>
#include <type_traits>

using namespace aletheia;

// ===========================================================================
// Type distinctness — every strong type is unique
// ===========================================================================

// String types (4 choose 2 = 6 pairs)
static_assert(!std::is_same_v<SignalName, MessageName>);
static_assert(!std::is_same_v<SignalName, NodeName>);
static_assert(!std::is_same_v<SignalName, Unit>);
static_assert(!std::is_same_v<MessageName, NodeName>);
static_assert(!std::is_same_v<MessageName, Unit>);
static_assert(!std::is_same_v<NodeName, Unit>);

// Numeric physical types (4 choose 2 = 6 pairs)
static_assert(!std::is_same_v<PhysicalValue, ScaleFactor>);
static_assert(!std::is_same_v<PhysicalValue, ScaleOffset>);
static_assert(!std::is_same_v<PhysicalValue, Delta>);
static_assert(!std::is_same_v<ScaleFactor, ScaleOffset>);
static_assert(!std::is_same_v<ScaleFactor, Delta>);
static_assert(!std::is_same_v<ScaleOffset, Delta>);

// Integer domain types (4 choose 2 = 6 pairs)
static_assert(!std::is_same_v<BitPosition, BitLength>);
static_assert(!std::is_same_v<BitPosition, PropertyIndex>);
static_assert(!std::is_same_v<BitPosition, MultiplexValue>);
static_assert(!std::is_same_v<BitLength, PropertyIndex>);
static_assert(!std::is_same_v<BitLength, MultiplexValue>);
static_assert(!std::is_same_v<PropertyIndex, MultiplexValue>);

// Cross-category: strong types don't alias raw types
static_assert(!std::is_same_v<PhysicalValue, double>);
static_assert(!std::is_same_v<BitPosition, std::uint16_t>);
static_assert(!std::is_same_v<BitLength, std::uint8_t>);

// ===========================================================================
// StandardId — validated construction (constexpr)
// ===========================================================================

static_assert(StandardId::create(0).has_value());
static_assert(StandardId::create(100).has_value());
static_assert(StandardId::create(2047).has_value());
static_assert(!StandardId::create(2048).has_value());
static_assert(!StandardId::create(65535).has_value());

static_assert(StandardId::create(0x100)->value() == 0x100);
static_assert(StandardId::create(0)->value() == 0);
static_assert(StandardId::create(2047)->value() == 2047);

// ===========================================================================
// ExtendedId — validated construction (constexpr)
// ===========================================================================

static_assert(ExtendedId::create(0).has_value());
static_assert(ExtendedId::create(2048).has_value()); // beyond standard range
static_assert(ExtendedId::create(536'870'911).has_value());
static_assert(!ExtendedId::create(536'870'912).has_value());

static_assert(ExtendedId::create(1'000'000)->value() == 1'000'000);

// ===========================================================================
// Dlc — validated construction (constexpr)
// ===========================================================================

static_assert(Dlc::create(0).has_value());
static_assert(Dlc::create(8).has_value());
static_assert(!Dlc::create(9).has_value());
static_assert(!Dlc::create(255).has_value());

static_assert(Dlc::create(4)->value() == 4);

// ===========================================================================
// Strong type accessors (constexpr)
// ===========================================================================

static_assert(PhysicalValue{42.0}.get() == 42.0);
static_assert(PhysicalValue{-1.5}.get() == -1.5);
static_assert(ScaleFactor{0.25}.get() == 0.25);
static_assert(ScaleOffset{-40.0}.get() == -40.0);
static_assert(Delta{100.0}.get() == 100.0);

static_assert(BitPosition{0}.get() == 0);
static_assert(BitPosition{63}.get() == 63);
static_assert(BitLength{1}.get() == 1);
static_assert(BitLength{64}.get() == 64);
static_assert(PropertyIndex{0}.get() == 0);
static_assert(MultiplexValue{42}.get() == 42);

// ===========================================================================
// Strong type comparison operators (constexpr)
// ===========================================================================

static_assert(PhysicalValue{1.0} == PhysicalValue{1.0});
static_assert(PhysicalValue{1.0} != PhysicalValue{2.0});
static_assert(PhysicalValue{1.0} < PhysicalValue{2.0});
static_assert(PhysicalValue{2.0} > PhysicalValue{1.0});
static_assert(PhysicalValue{1.0} <= PhysicalValue{1.0});
static_assert(PhysicalValue{1.0} >= PhysicalValue{1.0});

static_assert(BitPosition{0} < BitPosition{1});
static_assert(BitLength{8} == BitLength{8});
static_assert(MultiplexValue{1} != MultiplexValue{2});

static_assert(StandardId::create(100).value() == StandardId::create(100).value());
static_assert(StandardId::create(100).value() != StandardId::create(200).value());
static_assert(Dlc::create(4).value() < Dlc::create(8).value());

// ===========================================================================
// ByteOrder enum
// ===========================================================================

static_assert(ByteOrder::LittleEndian != ByteOrder::BigEndian);
static_assert(static_cast<int>(ByteOrder::LittleEndian) == 0);
static_assert(static_cast<int>(ByteOrder::BigEndian) == 1);

// ===========================================================================
// FramePayload layout
// ===========================================================================

static_assert(sizeof(FramePayload) == 8);
static_assert(std::is_same_v<FramePayload, std::array<std::byte, 8>>);

// ===========================================================================
// Timestamp is chrono microseconds
// ===========================================================================

static_assert(std::is_same_v<Timestamp, std::chrono::microseconds>);
static_assert(Timestamp{1'000'000}.count() == 1'000'000);
static_assert(Timestamp{0}.count() == 0);

// ===========================================================================
// CanId is variant of StandardId and ExtendedId
// ===========================================================================

static_assert(std::variant_size_v<CanId> == 2);
static_assert(std::is_same_v<std::variant_alternative_t<0, CanId>, StandardId>);
static_assert(std::is_same_v<std::variant_alternative_t<1, CanId>, ExtendedId>);

// ===========================================================================
// ErrorKind enum coverage
// ===========================================================================

static_assert(static_cast<int>(ErrorKind::Protocol) == 0);
static_assert(static_cast<int>(ErrorKind::Validation) == 1);
static_assert(static_cast<int>(ErrorKind::State) == 2);
static_assert(static_cast<int>(ErrorKind::Ffi) == 3);

// ===========================================================================
// LtlFormula variant — correct number of alternatives
// ===========================================================================

// LtlFormula inherits from variant — check the base
static_assert(std::variant_size_v<LtlFormula::variant> == 13);
static_assert(std::variant_size_v<Predicate> == 7);

// ===========================================================================
// Verdict enum
// ===========================================================================

static_assert(Verdict::Holds != Verdict::Fails);

// ===========================================================================
// IssueSeverity and IssueCode enums
// ===========================================================================

static_assert(IssueSeverity::Error != IssueSeverity::Warning);
static_assert(static_cast<int>(IssueCode::DuplicateMessageId) == 0);
static_assert(static_cast<int>(IssueCode::BitLengthExcessive) == 15);

// ===========================================================================
// AletheiaClient — non-copyable, movable
// ===========================================================================

static_assert(!std::is_copy_constructible_v<AletheiaClient>);
static_assert(!std::is_copy_assignable_v<AletheiaClient>);
static_assert(std::is_move_constructible_v<AletheiaClient>);
static_assert(std::is_move_assignable_v<AletheiaClient>);

// ===========================================================================
// IBackend — abstract (has pure virtuals)
// ===========================================================================

static_assert(std::is_abstract_v<IBackend>);
static_assert(std::has_virtual_destructor_v<IBackend>);

// ===========================================================================
// StrongString implicit conversion to string_view
// ===========================================================================

static_assert(std::is_convertible_v<SignalName, std::string_view>);
static_assert(std::is_convertible_v<MessageName, std::string_view>);
static_assert(std::is_convertible_v<NodeName, std::string_view>);
static_assert(std::is_convertible_v<Unit, std::string_view>);

// Strong<> does NOT convert implicitly
static_assert(!std::is_convertible_v<PhysicalValue, double>);
static_assert(!std::is_convertible_v<BitPosition, std::uint16_t>);

// ===========================================================================
// No implicit conversions between strong types
// ===========================================================================

static_assert(!std::is_convertible_v<SignalName, MessageName>);
static_assert(!std::is_convertible_v<PhysicalValue, ScaleFactor>);
static_assert(!std::is_convertible_v<BitPosition, BitLength>);

// ===========================================================================
// SignalPresence variant
// ===========================================================================

static_assert(std::variant_size_v<SignalPresence> == 2);
static_assert(std::is_same_v<std::variant_alternative_t<0, SignalPresence>, AlwaysPresent>);
static_assert(std::is_same_v<std::variant_alternative_t<1, SignalPresence>, Multiplexed>);

// ===========================================================================
// FrameResponse variant
// ===========================================================================

static_assert(std::variant_size_v<FrameResponse> == 2);
static_assert(std::is_same_v<std::variant_alternative_t<0, FrameResponse>, Ack>);
static_assert(std::is_same_v<std::variant_alternative_t<1, FrameResponse>, Violation>);

// If this file compiles, all 100+ static assertions pass.
int main() {
    return 0;
}
