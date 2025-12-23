(** * Usage Examples for Rocq Transformer *)

(** This module demonstrates how to:
    1. Create valid TransformerConfigs with divisibility proofs
    2. Construct model components
    3. Run type-checked forward passes
    4. Perform greedy decoding with length proofs *)

From Coq Require Import Init.Nat.
From Coq Require Import Arith.PeanoNat.
From Coq Require Import Lia.
From Transformer Require Import Tensor.
From Transformer Require Import Config.
From Transformer Require Import Linear.
From Transformer Require Import Embedding.
From Transformer Require Import Attention.
From Transformer Require Import FeedForward.
From Transformer Require Import Encoder.
From Transformer Require Import Decoder.
From Transformer Require Import Model.
From Transformer Require Import Inference.

(** * Example 1: Creating Valid Configurations *)

(** The type system requires proof that num_heads divides d_model.
    This prevents runtime errors from invalid head configurations. *)

(** A standard BERT-base like configuration: d_model=768, heads=12 *)
Lemma bert_heads_divide : (12 | 768).
Proof. exists 64. reflexivity. Qed.

Definition bertBaseConfig : TransformerConfig :=
  mkConfig 768 3072 12 12 512 bert_heads_divide.

(** A GPT-2 small like configuration: d_model=768, heads=12 *)
Definition gpt2SmallConfig : TransformerConfig := bertBaseConfig.

(** A smaller debug configuration: d_model=64, heads=4 *)
Lemma debug_heads_divide : (4 | 64).
Proof. exists 16. reflexivity. Qed.

Definition debugConfig : TransformerConfig :=
  mkConfig 64 256 4 2 128 debug_heads_divide.

(** Invalid configuration - this FAILS to compile:
    7 does not divide 512, so no proof exists *)
(*
Lemma bad_heads_divide : (7 | 512).
Proof. (* Cannot prove - would need 512 = 7 * k for some k *) Abort.

Definition badConfig : TransformerConfig :=
  mkConfig 512 2048 7 6 5000 bad_heads_divide.  (* Won't compile! *)
*)

(** * Example 2: Constructing Model Components *)

(** Multi-head attention requires proof that d_model is divisible by num_heads *)
Lemma mha_heads_divide : exists head_dim, 64 = 4 * head_dim.
Proof. exists 16. reflexivity. Qed.

Definition exampleMHA : MultiHeadAttention 64 4 :=
  initMultiHeadAttention 64 4 mha_heads_divide.

(** Feed-forward network: 64 -> 256 -> 64.
    Uses initFeedForward for weight initialization. *)
Definition exampleFFN : FeedForward 64 256 :=
  initFeedForward 64 256.

(** * Example 3: Type-Checked Forward Passes *)

(** Self-attention preserves dimensions - guaranteed by types *)
Definition selfAttentionExample
  (batch seq d_model : nat)
  (x : Tensor3D batch seq d_model)
  (mha : MultiHeadAttention d_model 8)
  (mask : option (Tensor3D batch seq seq))
  : Tensor3D batch seq d_model :=
  multiHeadAttentionForward mha x x x mask.
(* Return type MUST be Tensor3D batch seq d_model - compiler enforces this *)

(** Cross-attention uses query length for output *)
Definition crossAttentionExample
  (batch q_len k_len d_model : nat)
  (query : Tensor3D batch q_len d_model)
  (memory : Tensor3D batch k_len d_model)
  (mha : MultiHeadAttention d_model 8)
  : Tensor3D batch q_len d_model :=
  multiHeadAttentionForward mha query memory memory None.
(* Output has q_len rows, not k_len - type system proves this *)

(** * Example 4: Encoder-Decoder Model *)

(** Full encoder-decoder with vocabulary *)
Definition exampleModel : EncoderDecoder 64 256 4 2 128 1000 1000 :=
  initEncoderDecoder 64 256 4 2 128 1000 1000.

(** Encode source sequence - output has same shape.
    Requires proof that seq_len <= max_len. *)
Lemma encode_src_fits : 20 <= 128.
Proof. lia. Qed.

Definition encodeExample
  (src : Tensor2D 1 20)
  (srcMask : option (Tensor3D 1 20 20))
  : Tensor3D 1 20 64 :=
  encode exampleModel src srcMask encode_src_fits.

(** * Example 5: Greedy Decoding with Length Proofs *)

(** Greedy decode requires proofs about sequence lengths.
    This ensures positional encodings are valid. *)

(** Proof that source length fits in max_len *)
Lemma src_fits : 20 <= 128.
Proof. lia. Qed.

(** Proof that generation length fits in max_len *)
Lemma gen_fits : 50 <= 128.
Proof. lia. Qed.

(** Proof that we generate at least 1 token *)
Lemma gen_positive : 50 >= 1.
Proof. lia. Qed.

(** Type-checked translation: exactly 50 output tokens *)
Definition translateExample
  (src : Tensor2D 1 20)
  : Tensor2D 1 50 :=
  greedyDecode exampleModel src None 1 src_fits gen_fits gen_positive.
(* Return type Tensor2D 1 50 is PROVEN by the type system *)

(** * Example 6: Demonstrating Type Errors *)

(** These examples show what the type system catches at compile time. *)

(** ERROR: Mismatched residual dimensions
Definition brokenResidual
  (x : Tensor3D 32 128 512)
  (out : Tensor3D 32 128 256)  (* Wrong! Should be 512 *)
  : Tensor3D 32 128 512 :=
  add3D 32 128 512 x out.
  (* Type error: out has wrong last dimension *)
*)

(** ERROR: Invalid attention mask shape
Definition brokenMask
  (query : Tensor3D 32 10 512)
  (memory : Tensor3D 32 20 512)
  (mask : Tensor3D 32 10 10)  (* Wrong! Should be 10 x 20 *)
  (mha : MultiHeadAttention 512 8)
  : Tensor3D 32 10 512 :=
  multiHeadAttentionForward mha query memory memory (Some mask).
  (* Type error: mask should be Tensor3D 32 10 20 for cross-attention *)
*)

(** * Example 7: Working with Masks *)

(** Create causal mask for autoregressive decoding *)
Definition causalMaskExample (seq_len : nat) : Tensor2D seq_len seq_len :=
  subsequentMask seq_len.

(** Expand 2D mask to 3D for batching *)
Definition expandTo3D (batch seq_len : nat)
  (mask : Tensor2D seq_len seq_len)
  : Tensor3D batch seq_len seq_len :=
  expand_mask2D_to_3D batch seq_len mask.

(** Expand 3D mask to 4D for attention heads *)
Definition expandTo4D (batch seq_q seq_k : nat)
  (mask : Tensor3D batch seq_q seq_k)
  : Tensor4D batch 1 seq_q seq_k :=
  expand_mask3D_to_4D batch seq_q seq_k mask.

(** * Summary *)

(** Key type-level guarantees demonstrated:
    1. Config requires (num_heads | d_model) proof - no invalid configs
    2. Self-attention output type equals input type - residuals work
    3. Cross-attention uses query length - correct attention shape
    4. Greedy decode returns Tensor2D batch gen_len - exact length proven
    5. Masks must match attention dimensions - no shape mismatches *)
