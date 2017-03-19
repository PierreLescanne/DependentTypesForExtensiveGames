(* Time-stamp: "2017-03-06 18:41:24 libres" *)
(****************************************************************)
(*                      finite_Horizon.v                        *)
(*                                                              *)
(**          © Pierre Lescanne  (December 2015)                 *)
(*                                                              *)
(*              LIP (ENS-Lyon, CNRS, INRIA)                     *)
(*                                                              *)
(*                                                              *)
(*  Developed in  V8.6              January 2016 --Janvier 2017 *)
(****************************************************************)
Section FiniteHistory.

Add LoadPath ".".

Require Import games. 

Inductive AliceBob : Set := Alice | Bob.
Definition Choice: (AliceBob -> Set) :=
  fun a:AliceBob  => match a with Alice => nat | Bob => unit end.
Definition Utility: AliceBob -> Set := fun a => unit.

(* Utility is unit *)

Notation "<| f |>" := (gLeaf AliceBob Choice Utility f).
Notation "<| a , next |>" := (gNode AliceBob Choice Utility a next).

(* A finite threadlike game of length n *)
Fixpoint  ThreadlikeGame (n:nat): (Game AliceBob Choice Utility) :=
  match n with
    | 0 => <|fun (a:AliceBob) => match a with | Alice => tt
                                              | Bob => tt end|>
    | (S n) => <|Bob,fun c:Choice Bob
                     => match c with tt=>ThreadlikeGame n end|>
  end.

(* A game with a finite horizon *)
Definition GameWFH:(Game AliceBob Choice Utility)  :=
  <| Alice, fun n:Choice Alice => ThreadlikeGame n |>.

Proposition FiniteGameWFH: FiniteHistoryGame AliceBob Choice Utility GameWFH.
Proof.
  unfold GameWFH; apply finHorGNode; induction c;
  [apply finHorGLeaf |
   intros; apply finHorGNode; induction c0; assumption].
Qed.

End FiniteHistory.