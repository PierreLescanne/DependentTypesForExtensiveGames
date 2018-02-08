(* Time-stamp: "2018-02-08 18:18:31 pierre" *)
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
Section FiniteHistory.

Add LoadPath ".".

Require Import games_Choice_Dependent. 

Inductive AliceBob : Set := Alice | Bob.
Definition Choice :(AliceBob -> Set) :=
  fun a:AliceBob  => match a with Alice => nat | Bob => unit end.
(* Utility is unit *)

Notation "<| f |>" := (gLeaf AliceBob unit Choice f).
Notation "<| a , next |>" := (gNode AliceBob unit Choice a next).

(* A finite threadlike game of length n *)
Fixpoint  ThreadlikeGame (n:nat): (Game AliceBob unit Choice) :=
  match n with
    | 0 => <|fun (a:AliceBob) => match a with | Alice => tt
                                              | Bob => tt end|>
    | (S n) => <|Bob,fun c:Choice Bob
                     => match c with tt=>ThreadlikeGame n end|>
  end.

(* A game with a finite horizon *)
Definition GameWFH:(Game AliceBob unit Choice)  :=
  <| Alice, fun n:Choice Alice => ThreadlikeGame n |>.

Proposition FiniteHistoryGameWFH: FiniteHistoryGame AliceBob unit Choice GameWFH.
Proof.
  unfold GameWFH; apply finHorGNode; intro; elim c';
  [apply finHorGLeaf |
   intros; apply finHorGNode; induction c'0; assumption].
Qed.

End FiniteHistory.