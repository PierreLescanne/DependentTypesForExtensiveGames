(* Time-stamp: "2018-02-08 18:21:08 pierre" *)
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

Require Import games_Choice_Dependent yingYang dollar.

Arguments Divergent  [Agent Utility Choice] s.

(* preference on Utility *)
Require Import Relations.

Lemma AlwaysGoodAndDivergentInYingYang :
  exists (s:StratProf yingYang.AliceBob  YingYang yingYang.Choice),
    AlwaysGood yingYang.AliceBob YingYang yingYang.Choice eq s /\
    Divergent s.
Proof.
  exists yingYangAcBc.  
  split.
  apply AlwaysGoodYyAcBc.
  apply DivergenceYyAcBc.
Qed.

Lemma AlwaysGoodAndDivergentInDollar :
  exists (s:StratProf dollar.AliceBob nat dollar.Choice),
    AlwaysGood dollar.AliceBob nat dollar.Choice ge s /\
    Divergent s.
Proof.
  exists (dollarAcBc 0).
  split.
  apply AlwaysGoodDolAcBc.
  apply DivergenceDolAcBc.
Qed.

End Escalation.