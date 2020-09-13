(* Time-stamp: "2018-02-09 17:01:29 pierre" *)
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
Require Import games_Choice_Dependent yinYang dollar.
Require Import Relations.

Section Escalation.

Arguments Divergent  [Agent Utility Choice] s.

Lemma AlwaysGoodAndDivergentInYinYang :
  exists (s:StratProf yinYang.AliceBob  YinYang yinYang.Choice),
    AlwaysGood yinYang.AliceBob YinYang yinYang.Choice eq s /\
    Divergent s.
Proof.
  exists yinYangAcBc.  
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
