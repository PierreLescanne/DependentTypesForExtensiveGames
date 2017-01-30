(* Time-stamp: "2017-01-28 14:36:48 libres" *)
(****************************************************************)
(*                        escalation.v                          *)
(*                                                              *)
(**          © Pierre Lescanne  (December 2015)                 *)
(*                                                              *)
(*              LIP (ENS-Lyon, CNRS, INRIA)                     *)
(*                                                              *)
(*                                                              *)
(*  Developed in  V8.6                   January -- April 2016  *)
(****************************************************************)
Section Escalation.

Require Import games yingYang dollar.

Arguments Divergent  [Agent Choice Utility] s.

(* preference on Utility *)
Require Import Relations.

Lemma AlongGoodAndDivergentInYingYang :
  exists (s:StratProf yingYang.AliceBob yingYang.ChoiceYY yingYang.UtilityYY),
    AlongGood yingYang.AliceBob yingYang.ChoiceYY yingYang.UtilityYY eqYY s /\
    Divergent s.
Proof.
  exists yingYangAcBc.  
  split.
  apply AlongGoodYyAcBc.
  apply DivergenceYyAcBc.
Qed.

Lemma AlongGoodAndDivergentInDollar :
  exists (s:StratProf dollar.AliceBob dollar.ChoiceDol dollar.UtilityDol),
    AlongGood dollar.AliceBob dollar.ChoiceDol dollar.UtilityDol dollar.geDol s /\
    Divergent s.
Proof.
  exists (dollarAcBc 0).
  split.
  apply AlongGoodDolAcBc.
  apply DivergenceDolAcBc.
Qed.

End Escalation.