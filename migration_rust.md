# MITL2Timed Migration to Rust Strategy & Plan

## 1. Executive Summary & Goals
This document outlines the architecture, data structures, and phase-by-phase migration plan to rewrite `MITL2Timed` (Metric Interval Temporal Logic to Timed Automata translator) from C to **idiomatic, high-performance, safe Rust**.

The C implementation relied heavily on raw pointers, manual memory pools, bit-packed integer arrays for set representations, and recursive linked list structures (`Node`, `TTrans`, `ATrans`, `CGuard`, `Symbol`). This introduced buffer overflows, memory leaks, unsafe pointer arithmetic, and segmentation faults when translating complex MITL formulas.

By migrating to Rust, we aim to achieve:
1. **Memory Safety & Zero Undefined Behavior**: Eliminate memory leaks, double frees, and segmentation faults without needing custom manual freelists or raw pointers.
2. **Idiomatic Data Structures**: Replace manual linked lists and raw pointers with standard Rust ownership, `Vec`, `Box`, `Option`, enums with rich data payloads, and `HashSet` / `BTreeSet` or `bitvec`.
3. **Type Safety & Maintainability**: Leverage Rust's algebraic data types (enums) to represent AST nodes, clock constraints, automaton states, and transitions cleanly.
4. **CLI & Compatibility**: Provide a CLI binary compatible with existing flags (`-f`, `-F`, `-t spin|dot|gexf`, `-s`, etc.) and output format.

---

## 2. Current Architecture vs. Proposed Rust Architecture

### 2.1 Formula AST Representation
In C:
```c
typedef struct Node {
    short ntyp;
    float intvl[2];
    struct Symbol *sym;
    struct Node *lft;
    struct Node *rgt;
    struct Node *nxt;
} Node;
```

In Rust (Idiomatic Enum AST):
```rust
#[derive(Debug, Clone, PartialEq)]
pub enum Formula {
    True,
    False,
    Predicate(String),
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Until(Box<Formula>, Box<Formula>),
    Release(Box<Formula>, Box<Formula>),
    Next(Box<Formula>),
    EventuallyI {
        interval: (f32, f32),
        formula: Box<Formula>,
    },
    AlwaysI {
        interval: (f32, f32),
        formula: Box<Formula>,
    },
}
```

### 2.2 Clock Guards & Invariants
In C:
```c
typedef struct CCstr {
    int cIdx;
    unsigned short gType;
    int bndry;
} CCstr;

typedef struct CGuard {
    int nType;
    CCstr *cCstr;
    struct CGuard *lft;
    struct CGuard *rgt;
} CGuard;
```

In Rust:
```rust
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RelOp {
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ClockConstraint {
    pub clock_idx: usize,
    pub op: RelOp,
    pub boundary: i32,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ClockGuard {
    Predicate(ClockConstraint),
    And(Box<ClockGuard>, Box<ClockGuard>),
    Or(Box<ClockGuard>, Box<ClockGuard>),
    Start { clock_idx: usize },
    Stop { start_idx: usize, end_idx: usize },
}
```

### 2.3 Timed Automata Representation
In C, transitions (`TTrans`) form a linked list pointing to `TState` pointers across dynamically sized arrays.
In Rust, we represent states and transitions using index-based graph representations (`Vec<State>`, `Vec<Transition>`):

```rust
#[derive(Debug, Clone)]
pub struct State {
    pub id: String,
    pub invariant: Option<ClockGuard>,
    pub input_symbols: Vec<u16>,
    pub output_symbol: u16,
    pub is_buchi: bool,
    pub symbols: BTreeSet<usize>,
}

#[derive(Debug, Clone)]
pub struct Transition {
    pub from: usize,
    pub to: usize,
    pub reset_clocks: BTreeSet<usize>,
    pub guard: Option<ClockGuard>,
}

#[derive(Debug, Clone, Default)]
pub struct TimedAutomaton {
    pub states: Vec<State>,
    pub transitions: Vec<Transition>,
    pub event_transitions: Vec<Transition>,
}
```

---

## 3. Migration Roadmap & Phases

### Phase 1: Project Setup & Lexer/Parser Module
- **Goal**: Create a new Cargo crate `mitl2ta-rs`.
- **Tasks**:
  - Set up `nom` or `pest` for lexing and parsing MITL formulas.
  - Parse boolean operators (`!`, `&&`, `||`), temporal operators (`U`, `V`, `X`), and interval operators (`<>_[a,b]`, `[]_[a,b]`).
  - Unit test parser against sample formulas (`p U q`, `<>_[1,2] (a)`).

### Phase 2: Core AST & Simplification/Rewrite Module
- **Goal**: Implement formula normalization and rewriting.
- **Tasks**:
  - Implement negation normal form (NNF) transformation (`push_negation`).
  - Implement canonicalization / caching equivalent formulas.

### Phase 3: Timed Automaton Building Core
- **Goal**: Re-implement translation logic from MITL AST to `TimedAutomaton`.
- **Tasks**:
  - Implement `build_timed` recursive translator for atomic predicates, temporal operators, and interval operators (`EventuallyI`).
  - Implement prediction generators (`Gen`) and prediction checkers (`CHK`) for timed bounds.
  - Implement automata product/merging logic (`merge_timed`, `merge_bin_timed`, `merge_event_timed`, `merge_map_timed`).

### Phase 4: Output Generators & Export Modules
- **Goal**: Re-create export outputs.
- **Tasks**:
  - Implement UPPAAL Python script exporter (`timed_to_xml` replacement).
  - Implement dot, spin, and gexf output formatters.

### Phase 5: CLI & Testing Harness
- **Goal**: Build `mitl2ta` executable and verify equivalence with C implementation.
- **Tasks**:
  - Implement CLI with `clap`.
  - Add end-to-end integration tests comparing output against the C baseline across formula sets in `demo/`.

---

## 4. Key Benefits of Rust Migration

| Feature | C Implementation | Rust Implementation |
|---|---|---|
| **Memory Management** | Custom freelist + manual `malloc`/`free` | Safe automatic RAII (`Box`, `Vec`) |
| **Safety** | Risk of buffer overflow (`sprintf`), use-after-free | Checked array bounds, zero unsafe code |
| **Graph Traversal** | Linked list pointer chasing | Array indices (`usize`), contiguous memory |
| **Error Handling** | `Fatal()` calls `exit(1)` abruptly | `Result<T, Error>` with context |
| **Maintainability** | Monolithic file (`timed.c` >3000 lines) | Modular crate structure (`ast`, `parser`, `automaton`, `cli`) |
