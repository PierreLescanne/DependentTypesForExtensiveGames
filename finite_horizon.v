(* Time-stamp: "2016-06-06 23:44:19 pierre" *)
(****************************************************************)
(*                      finite_Horizon.v                        *)
(*                                                              *)
(**          © Pierre Lescanne  (December 2015)                 *)
(*                                                              *)
(*              LIP (ENS-Lyon, CNRS, INRIA)                     *)
(*                                                              *)
(*                                                              *)
(*  Developed in  V8.4pl4              January May 20016        *)
(****************************************************************)
Section FiniteHorizon.

Add LoadPath ".".

Require Import games. 

Inductive AliceBob : Set := Alice | Bob.
Definition Choice :(AliceBob -> Set) :=
  fun a:AliceBob  => match a with Alice => nat | Bob => unit end.
(* Utility is unit *)

Notation "<| f |>" := (gLeaf AliceBob Choice  unit f).
Notation "<| a , next |>" := (gNode AliceBob Choice unit a next).

(* A finite threadlike game of length n *)
Fixpoint  ThreadlikeGame (n:nat): (Game AliceBob Choice unit) :=
  match n with
    | 0 => <|fun (a:AliceBob) => match a with Alice => tt
                                           | Bob => tt end|>
    | (S n) => <|Bob,fun c:Choice Bob
                     => match c with tt=>ThreadlikeGame n end|>
  end.

(* A game with a finite horizon *)
Definition GameWFH:(Game AliceBob Choice unit)  :=
  <| Alice, fun n:Choice Alice => ThreadlikeGame n |>.

Proposition FiniteHorizonGameWFH: FiniteHorizonGame AliceBob Choice  unit GameWFH.
Proof.
  unfold GameWFH; apply finHorGNode; intro; elim c';
  [apply finHorGLeaf |
   intros; apply finHorGNode; induction c'0; assumption].
Qed.

End FiniteHorizon.