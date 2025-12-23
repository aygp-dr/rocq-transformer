(** * Semantic Axioms for Transformer Operations *)

(** This module extends the structural type guarantees with semantic axioms
    about the mathematical behavior of numerical operations.

    These axioms capture properties like:
    - softmax outputs sum to 1 (probability distribution)
    - layerNorm outputs have zero mean and unit variance
    - attention weights are non-negative

    These are stated as axioms because proving them would require
    a formal model of floating-point arithmetic. *)

From Coq Require Import Init.Nat.
From Coq Require Import Lists.List.
From Coq Require Import Reals.Reals.
From Coq Require Import Reals.RIneq.
Import ListNotations.

Open Scope R_scope.

(** ** Abstract Value Types *)

(** We use R (real numbers) as abstract tensor values for semantic reasoning. *)

Definition RealTensor1D := list R.
Definition RealTensor2D := list (list R).
Definition RealTensor3D := list (list (list R)).

(** ** Summation over tensors *)

Fixpoint sum_list (l : RealTensor1D) : R :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

Definition sum_rows (t : RealTensor2D) : RealTensor1D :=
  List.map sum_list t.

(** ** Softmax Semantic Axioms *)

(** Abstract softmax function on real-valued vectors *)
Parameter softmax_real : RealTensor1D -> RealTensor1D.

(** Axiom: softmax preserves length *)
Axiom softmax_preserves_length : forall (v : RealTensor1D),
  List.length (softmax_real v) = List.length v.

(** Axiom: softmax outputs are non-negative *)
Axiom softmax_nonneg : forall (v : RealTensor1D) (x : R),
  In x (softmax_real v) -> x >= 0.

(** Axiom: softmax outputs sum to 1 (probability distribution) *)
Axiom softmax_sums_to_one : forall (v : RealTensor1D),
  (List.length v > 0)%nat ->
  sum_list (softmax_real v) = 1.

(** Axiom: softmax is monotonic (larger inputs -> larger outputs) *)
Axiom softmax_monotonic : forall (v : RealTensor1D) (i j : nat) (vi vj pi pj : R),
  nth i v 0 = vi ->
  nth j v 0 = vj ->
  nth i (softmax_real v) 0 = pi ->
  nth j (softmax_real v) 0 = pj ->
  vi > vj -> pi > pj.

(** ** Layer Normalization Semantic Axioms *)

(** Abstract layernorm function *)
Parameter layernorm_real : RealTensor1D -> RealTensor1D.

(** Axiom: layernorm preserves length *)
Axiom layernorm_preserves_length : forall (v : RealTensor1D),
  List.length (layernorm_real v) = List.length v.

(** Mean computation *)
Definition mean (v : RealTensor1D) : R :=
  match List.length v with
  | 0 => 0
  | n => sum_list v / INR n
  end.

(** Axiom: layernorm output has zero mean *)
Axiom layernorm_zero_mean : forall (v : RealTensor1D),
  (List.length v > 0)%nat ->
  mean (layernorm_real v) = 0.

(** Variance computation *)
Definition variance (v : RealTensor1D) : R :=
  let m := mean v in
  let squared_diffs := List.map (fun x => (x - m) * (x - m)) v in
  match List.length v with
  | 0 => 0
  | n => sum_list squared_diffs / INR n
  end.

(** Axiom: layernorm output has unit variance (approximately, before scale/shift) *)
Axiom layernorm_unit_variance : forall (v : RealTensor1D),
  (List.length v > 1)%nat ->
  variance (layernorm_real v) = 1.

(** ** Attention Weight Axioms *)

(** Attention weights after softmax form a probability distribution over keys *)
Parameter attention_weights : RealTensor2D -> RealTensor2D -> RealTensor2D.

(** Axiom: each row of attention weights sums to 1 *)
Axiom attention_weights_normalized : forall (Q K : RealTensor2D) (row : RealTensor1D),
  In row (attention_weights Q K) ->
  (List.length row > 0)%nat ->
  sum_list row = 1.

(** Axiom: attention weights are non-negative *)
Axiom attention_weights_nonneg : forall (Q K : RealTensor2D) (row : RealTensor1D) (w : R),
  In row (attention_weights Q K) ->
  In w row ->
  w >= 0.

(** ** Dropout Semantic Axioms *)

(** Dropout at inference (with probability 0) is identity *)
Parameter dropout_inference : RealTensor1D -> RealTensor1D.

Axiom dropout_inference_identity : forall (v : RealTensor1D),
  dropout_inference v = v.

(** ** ReLU Semantic Axioms *)

Parameter relu_real : RealTensor1D -> RealTensor1D.

(** Axiom: ReLU outputs are non-negative *)
Axiom relu_nonneg : forall (v : RealTensor1D) (x : R),
  In x (relu_real v) -> x >= 0.

(** Axiom: ReLU preserves non-negative inputs *)
Axiom relu_preserves_positive : forall (v : RealTensor1D) (i : nat) (vi : R),
  nth i v 0 = vi ->
  vi >= 0 ->
  nth i (relu_real v) 0 = vi.

(** Axiom: ReLU zeros negative inputs *)
Axiom relu_zeros_negative : forall (v : RealTensor1D) (i : nat) (vi : R),
  nth i v 0 = vi ->
  vi < 0 ->
  nth i (relu_real v) 0 = 0.

(** ** Embedding Semantic Axioms *)

(** Different tokens map to different embeddings *)
Parameter embedding_lookup : nat -> nat -> RealTensor1D.

Axiom embedding_dimension : forall (vocab_size d_model token : nat),
  (token < vocab_size)%nat ->
  (List.length (embedding_lookup vocab_size token) = d_model)%nat.

(** ** Scale Invariance *)

(** Scaling query/key by 1/sqrt(d_k) doesn't change relative ordering *)
Parameter scale_real : R -> RealTensor1D -> RealTensor1D.

Axiom scale_preserves_order : forall (c : R) (v : RealTensor1D) (i j : nat),
  c > 0 ->
  nth i v 0 > nth j v 0 ->
  nth i (scale_real c v) 0 > nth j (scale_real c v) 0.

Close Scope R_scope.
