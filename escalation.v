(* Time-stamp: "2016-05-03 22:23:52 pierre" *)
(****************************************************************)
(*                        escalation.v                          *)
(*                                                              *)
(**          © Pierre Lescanne  (December 2015)                 *)
(*                                                              *)
(*              LIP (ENS-Lyon, CNRS, INRIA)                     *)
(*                                                              *)
(*                                                              *)
(*  Developed in  V8.4pl4                January -- April 2016  *)
(****************************************************************)
Section Escalation.

Require Import games yingYang dollar.

Notation "↑ s " := (Divergent yingYang.AliceBob yingYang.Choice YingYang s) (at level 5).

(* preference on Utility *)
Require Import Relations.

Lemma AlwaysGoodAndDivergentInYingYang :
  exists (s:StratProf yingYang.AliceBob yingYang.Choice YingYang),
    AlwaysGood yingYang.AliceBob yingYang.Choice YingYang eq s /\ (↑ s).
Proof.
  exists yingYangAcBc.  
  split.
  apply AlwaysGoodYyAcBc.
  apply DivergenceYyAcBc.
Qed.

Notation "↑ s " := (Divergent dollar.AliceBob dollar.Choice nat s) (at level 5).

Lemma AlwaysGoodAndDivergentInDollar :
  exists (s:StratProf dollar.AliceBob dollar.Choice nat),
    AlwaysGood dollar.AliceBob dollar.Choice nat ge s /\ (↑ s).
Proof.
  exists (dollarAcBc 0).
  split.
  apply AlwaysGoodDolAcBc.
  apply DivergenceDolAcBc.
Qed.

End Escalation.