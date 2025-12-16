# Contributing Guide

Thank you for your interest in contributing to this project. This document describes *how* to contribute and, just as importantly, *what kinds of contributions are expected to live upstream* versus outside the core.

The goal is to keep the core small, stable, and generally useful, while allowing users—individuals and companies alike—to adapt the software to their specific needs without friction.

---

## License

This project is licensed under the **BSD 2-Clause License**. By contributing, you agree that your contributions will be released under the same license.

This permissive license is intentional: it allows broad adoption, including in proprietary environments, while relying on architecture and process (not legal compulsion) to keep the project healthy.

---

## Design Philosophy

Before proposing changes, it helps to understand the project’s design priorities:

- The core should remain **small, coherent, and opinionated**
- Customization should happen via **extension points**, not by modifying core files
- General improvements should benefit *most* users
- Product-specific or environment-specific logic should live outside the core

Changes that reinforce these principles are the most likely to be accepted.

---

## Extension Points (Preferred Customization Mechanism)

If you are adapting the software for a specific use case, you should first look for an extension point rather than modifying existing files.

Examples of extension mechanisms include:

- Plugins or dynamically loaded modules
- Hooks or callbacks
- Strategy objects passed into APIs
- Configuration-driven behavior
- Wrappers around the command-line interface or Python modules

If you believe a missing extension point would be generally useful, proposing *the extension point itself* is often preferable to proposing a specialized feature.

---

## What Belongs Upstream

The following types of contributions are strongly encouraged:

- Bug fixes
- Performance improvements
- Refactoring for clarity or maintainability
- Simplifying APIs or reducing duplication
- Improving error handling or diagnostics
- Better documentation or examples
- Adding extension points that enable new use cases

These changes tend to reduce long-term maintenance cost for everyone, including downstream users.

---

## What Typically Stays Private

The following kinds of changes are usually *not* expected to be upstreamed:

- Product-specific integrations
- Customer-specific workflows
- Internal naming, conventions, or data models
- Code that reveals proprietary architecture or business logic
- One-off features useful to a single deployment

Keeping these changes private is acceptable and expected. You do not need to upstream everything to be a “good citizen.”

---

## Proposing Larger Changes

For non-trivial changes—especially refactors or API changes—please follow this process:

1. **Open an issue first** describing the problem you are trying to solve
2. Explain *why* the change is needed, not just *what* you plan to do
3. Discuss alternative approaches if relevant
4. Wait for maintainer feedback before investing heavily in implementation

This helps avoid duplicated effort and ensures that changes align with the project’s direction.

---

## Upstream-First Guideline

If you are working on a change that you believe would be generally useful:

- Prefer proposing it upstream *before* carrying it in a private fork
- If that is not possible, consider documenting the motivation publicly (issue or discussion) before implementation

This is not a requirement, but it helps establish clear provenance and reduces long-term friction.

---

## Coding Standards

Please follow the existing style and structure of the codebase:

- Keep changes focused and minimal
- Avoid mixing refactors with functional changes
- Write clear commit messages explaining intent
- Add tests where appropriate

Consistency matters more than personal preference.

---

## Maintainer Decisions

The maintainer reserves the right to:

- Request changes or simplifications
- Defer or reject features that increase core complexity
- Prioritize long-term maintainability over short-term convenience

These decisions are made to protect the project’s coherence and sustainability.

---

## Employer Contributions

Contributions made as part of employment are welcome, but they require particular care around scope and permissions.

If you are contributing on behalf of an employer:

- Ensure you have the right to contribute the code under the BSD 2-Clause license
- Prefer contributing **general improvements** (bug fixes, refactors, performance, documentation)
- Keep product-specific integrations or customer-specific logic outside the core

If a change was developed primarily for a proprietary product but appears generally useful, consider one of the following before submitting it upstream:

- Propose the change conceptually (issue or design discussion) before contributing code
- Ask your employer explicitly whether the change may be contributed upstream
- Split the work so that only the generally useful portion is submitted

Maintainers may ask for clarification about contribution provenance for larger changes. This is not adversarial; it is meant to protect both contributors and their employers.

---

## Final Notes

Contributions are welcome from individuals and organizations of all sizes. The project aims to be a reliable core that others can build upon—whether openly or privately.

If in doubt about whether a change belongs upstream, open a discussion. Asking early is always cheaper than rewriting later.

