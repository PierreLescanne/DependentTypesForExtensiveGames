(* Time-stamp: "2017-02-07 13:51:37 pierre" *)
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
  exists (s:StratProf yingYang.Agent yingYang.Choice yingYang.Utility),
    AlongGood yingYang.Agent yingYang.Choice yingYang.Utility yingYang.pref s
    /\ Divergent s.
Proof.
  exists yingYangAcBc.  
  split.
  apply AlongGoodYyAcBc.
  apply DivergenceYyAcBc.
Qed.

Lemma AlongGoodAndDivergentInDollar :
  exists (s:StratProf dollar.Agent dollar.Choice dollar.Utility),
    AlongGood dollar.Agent dollar.Choice dollar.Utility dollar.pref s
    /\ Divergent s.
Proof.
  exists (dollarAcBc 0).
  split.
  apply AlongGoodDolAcBc.
  apply DivergenceDolAcBc.
Qed.

End Escalation.