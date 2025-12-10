# Rocq Annotated Transformer

Formally verified Transformer architecture in Rocq/Coq, providing compile-time guarantees for tensor dimension safety.

## Build Commands

```bash
nix develop              # Enter dev shell with Coq 8.18
make                     # Build all modules
make clean               # Clean build artifacts
make RocqTransformer/Tensor.vo  # Build specific module
coqide                   # Launch CoqIDE for interactive development
```

## Quick Start

```bash
nix develop
make
```

## Module Hierarchy

```
RocqTransformer/
├── Tensor.v        -- Abstract tensor types with dimension tracking
├── Config.v        -- TransformerConfig with divisibility proofs
├── Linear.v        -- Linear layer abstraction
├── Embedding.v     -- Token embeddings + positional encoding
├── LayerNorm.v     -- Layer normalization
├── FeedForward.v   -- Position-wise FFN
├── Attention.v     -- Multi-head attention with Q/K compatibility
├── Sublayer.v      -- Sublayer connection (pre-norm residual)
├── Encoder.v       -- Encoder layer and stack
├── Decoder.v       -- Decoder layer with causal masking
├── Model.v         -- Complete EncoderDecoder model
├── Inference.v     -- Greedy decode with type-level guarantees
└── Properties.v    -- Cross-module architectural proofs
```

## Key Type-Level Guarantees

1. **Dimension preservation**: Operations maintain correct tensor shapes
2. **Q/K compatibility**: Query and Key must have same d_k dimension
3. **Divisibility**: d_model is divisible by num_heads (enforced in Config)
4. **Sequence bounds**: Positional encoding enforces seq_len <= max_len
5. **Residual connections**: Input and output shapes match

## Architecture

This is an abstract specification focusing on dimension safety rather than actual computation. Operations are axiomatized as `Parameter` declarations with correct type signatures, allowing the type system to verify dimensional correctness at compile time.

### Key Types

```coq
(* Tensor indexed by dimension list *)
Inductive Tensor : DimSpec -> Type := ...

(* Type aliases *)
Definition Tensor2D (rows cols : nat) := Tensor [rows; cols].
Definition Tensor3D (batch rows cols : nat) := Tensor [batch; rows; cols].
Definition Tensor4D (b h r c : nat) := Tensor [b; h; r; c].

(* Configuration with divisibility proof *)
Record TransformerConfig := {
  d_model : nat;
  num_heads : nat;
  heads_divide : (num_heads | d_model);  (* Compile-time proof *)
  ...
}.
```

## Nix Flake

The project uses a Nix flake for reproducible builds:

- `nix develop` - Development shell with Coq 8.18 and CoqIDE
- `nix build` - Build the compiled .vo files
- `nix flake check` - Verify everything compiles

## Relation to Haskell Implementation

This Rocq implementation corresponds to the Haskell Annotated Transformer at:
https://github.com/jwiegley/hs-annotated-transformer

The Rocq version provides formal verification of dimension constraints that are only documented in comments in the Haskell version.
