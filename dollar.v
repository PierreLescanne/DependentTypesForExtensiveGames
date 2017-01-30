(* Time-stamp: "2017-01-27 16:40:26 libres" *)
(****************************************************************)
(*                        dollar.v                              *)
(*                                                              *)
(**          © Pierre Lescanne  (December 2015)                 *)
(*                                                              *)
(*              LIP (ENS-Lyon, CNRS, INRIA)                     *)
(*                                                              *)
(*                                                              *)
(*  Developed in  V8.6            January 2016 -- Januar 2017   *)
(****************************************************************)
Section Dollar.

Add LoadPath ".". 

Require Import games.
Require Import Omega.
Require Import Relations.

(* Setting sets for agents and choices *)
Inductive AliceBob : Set := | Alice | Bob.
Inductive DorR : Set := | d | r.
Definition ChoiceDol: AliceBob -> Set := fun a => DorR.
Definition UtilityDol: AliceBob -> Set := fun a => nat.
Definition geDol: forall a: AliceBob, relation (UtilityDol a) :=
  fun a :AliceBob => fun x:UtilityDol a => fun y:UtilityDol a => ge x y.

Arguments StratProf [Agent Choice Utility].
Arguments Game [Agent Choice Utility].
Arguments UAssignment [Agent Choice Utility] s H a.
Arguments game [Agent Choice Utility] s.
Arguments Convergent [Agent Choice Utility] s.
Arguments AlwaysConvergent [Agent Choice Utility] s.
Arguments convLeaf [Agent Choice Utility] f.
Arguments convNode [Agent Choice Utility] a c next _.
Arguments StratProf_identity [Agent Choice Utility] s.
Arguments SPE [Agent Choice Utility] pref  s.
Arguments Uassign [Agent Choice Utility] s u.
Arguments good [Agent Choice Utility] pref s.
Arguments gEqual [Agent Choice Utility] g1 g2.
Arguments Divergent  [Agent Choice Utility] s.
Arguments AlongGood  [Agent Choice Utility] pref s.

Notation "<< f >>" := (sLeaf AliceBob ChoiceDol UtilityDol f).
Notation "<< a , c , next >>" := 
  (sNode AliceBob ChoiceDol UtilityDol a c next).
Notation "[ x , y ]" := 
  (fun a:AliceBob => match a as AliceBob return (UtilityDol a) with Alice => x | Bob => y end).
Notation "<| f |>" := (gLeaf  AliceBob nat Choice f).
Notation "<| a , next |>" := (gNode AliceBob ChoiceDol UtilityDol a next).

Notation "s1 +++ s2" := 
  (fun c:DorR => match c with d => s1 | r => s2 end) 
  (at level 30).
Notation "↓ s " := (Convergent s) (at level 5).
Notation "⇓ s" := (AlwaysConvergent s)
                    (at level 15).
Notation "↑ s " := (Divergent s) (at level 5).
Notation "g == g'" := (gEqual g g') (at level 80).

Ltac decomp := rewrite <- StratProf_decomposition;  simpl.
Ltac solvegeDol :=  unfold geDol;  omega.

(* --------------------------------- *)
(**    Dollar Auction                *)
(* --------------------------------- *)

(* Definitions *)
CoFixpoint dollarAcBs n := <<Alice, r, <<[n+1,n]>> +++ dollarBsAc n>>
  with dollarBsAc n := <<Bob, d, <<[n+1,n+1]>> +++ dollarAcBs (n+1)>>.

CoFixpoint dollarAsBc n := <<Alice, d, <<[n+1,n]>> +++ dollarBcAs n>>
  with dollarBcAs n := <<Bob, r, <<[n+1,n+1]>> +++ dollarAsBc (n+1)>>.

CoFixpoint dollarAcBc n := <<Alice, r, <<[n+1,n]>> +++ dollarBcAc n>>
  with dollarBcAc n := <<Bob, r, <<[n+1,n+1]>> +++ dollarAcBc (n+1)>>.

(* Lemmas on utility assignments *)

(* A continues Bob stops *)

Lemma UassignDolAcBs: forall n, Uassign (dollarAcBs n) [n+1,n+1].
Proof.
  intro n.
  rewrite <- StratProf_decomposition with (s:=dollarAcBs n); simpl.
  rewrite <- StratProf_decomposition with (s:=dollarBsAc n); simpl.
  apply UassignNode.
  apply UassignNode.
  apply UassignLeaf.  
Qed.

Lemma UassignDolBsAc: forall n, Uassign (dollarBsAc n) [n+1,n+1].
Proof.
  intro n.
  rewrite <- StratProf_decomposition with (s:=dollarBsAc n); simpl.
  apply UassignNode.
  apply UassignLeaf.  
Qed.

(* A stops Bob continues *)
Lemma UassignDolAsBc: forall n, Uassign (dollarAsBc n) [n+1,n].
Proof.
  intro n.
  rewrite <- StratProf_decomposition with (s:=dollarAsBc n); simpl.
  apply UassignNode.
  apply UassignLeaf.  
Qed.

Lemma UassignDolBcAs: forall n, Uassign (dollarBcAs n) [n+1+1,n+1].
Proof.
  intro n.
  rewrite <- StratProf_decomposition with (s:=dollarBcAs n); simpl.
  apply UassignNode.
  apply UassignDolAsBc.  
Qed.

(* Lemmas on Convergence of strategy profiles *)

Lemma ConvergentDolBsAc: forall n, ↓ (dollarBsAc n).
Proof.
  intro n; decomp; apply ConvNode; apply ConvLeaf.
Qed.

Lemma ConvergentDolAcBs: forall n, ↓ (dollarAcBs n).
Proof.
  intro n; decomp; apply ConvNode; apply ConvergentDolBsAc.
Qed.

Lemma ConvergentDolAsBc: forall n, ↓ (dollarAsBc n).
Proof.
  intro n; decomp; apply ConvNode; apply ConvLeaf.
Qed.

Lemma ConvergentDolBcAs: forall n, ↓ (dollarBcAs n).
Proof.
  intro n; decomp; apply ConvNode; apply ConvergentDolAsBc.
Qed.

(* Lemmas on Always Convergence of strategy profiles *)

Lemma AlwsConvDolAcBs: forall n, ⇓ (dollarAcBs n).
Proof.
  cofix AlwsConvDolAcBs. 
  intro n;
  decomp;
  apply AlwaysNode; [apply ConvNode; apply ConvergentDolBsAc |
                     induction c';
                       [apply AlwaysLeaf | decomp; apply AlwaysNode];
                       [apply ConvNode; apply ConvLeaf |
                        induction c'; [apply AlwaysLeaf | apply AlwsConvDolAcBs]]].
Qed.

Lemma AlwsConvDolBsAc: forall n, ⇓ (dollarBsAc n).
Proof.
  intro n;
  decomp; apply AlwaysNode;
  [apply ConvNode; apply ConvLeaf | 
   induction c';
     [apply AlwaysLeaf |
      apply AlwsConvDolAcBs]].
Qed.

Lemma AlwsConvDolBcAs: forall n, ⇓ (dollarBcAs n).
Proof.
  cofix AlwsConvDolBcAs;
  intro;
  decomp; apply AlwaysNode;
  [apply ConvNode; apply ConvergentDolAsBc |
   induction c';
     [apply AlwaysLeaf | 
      decomp; apply AlwaysNode;  
      [apply ConvNode; apply ConvLeaf |
       induction c';  [apply AlwaysLeaf | apply AlwsConvDolBcAs]]]].
Qed.

Lemma AlwsConvDolAsBc:forall n,  ⇓ (dollarAsBc n).
Proof.
  intro n;
  decomp; apply AlwaysNode;
  [apply ConvNode; apply ConvLeaf | 
   induction c'; [apply AlwaysLeaf | apply AlwsConvDolBcAs]].
Qed.

(* Equality of the underlying game *) 
Lemma sameGameBcAc_BsAc: forall n, game (dollarBcAc n) == game (dollarBsAc n).
Proof.
  cofix sameGameBcAc_BsAc;
  intro n;
  rewrite <- StratProf_decomposition with (s:=dollarBcAc n);
  rewrite <- StratProf_decomposition with (s:=dollarBsAc n);
  simpl;
  rewrite gameNode; rewrite gameNode; apply gEqualNode;
  induction c; [apply refGEqual | 
                rewrite <- StratProf_decomposition with (s:=dollarAcBc (n+1));
                  rewrite <- StratProf_decomposition with (s:=dollarAcBs (n+1));
                  simpl;
                  rewrite gameNode; rewrite gameNode; apply gEqualNode];
  induction c; [apply refGEqual | apply sameGameBcAc_BsAc].
Qed.

Lemma sameGameAcBc_AcBs: forall n, game (dollarAcBc n) == game (dollarAcBs n).
Proof.
  intro n;
  rewrite <- StratProf_decomposition with (s:=dollarAcBc n);
  rewrite <- StratProf_decomposition with (s:=dollarAcBs n);
  simpl;
  rewrite gameNode; rewrite gameNode; apply gEqualNode;
  induction c; [apply refGEqual | apply sameGameBcAc_BsAc].
Qed.

Lemma sameGameBcAs_BcAc: forall n, game (dollarBcAc n) == game (dollarBcAs n).
Proof.
  cofix sameGameBcAc_BsAc;
  intro n;
  rewrite <- StratProf_decomposition with (s:=dollarBcAc n);
  rewrite <- StratProf_decomposition with (s:=dollarBcAs n);
  simpl;
  rewrite gameNode; rewrite gameNode; apply gEqualNode;
  induction c;
  [apply refGEqual |
  rewrite <- StratProf_decomposition with (s:=dollarAcBc (n+1));
  rewrite <- StratProf_decomposition with (s:=dollarAsBc (n+1));
  simpl;
  rewrite gameNode; rewrite gameNode; apply gEqualNode;
  induction c; [apply refGEqual | apply sameGameBcAc_BsAc]].
Qed.

Lemma sameGameAcBc_AsBc: forall n, game (dollarAcBc n) == game (dollarAsBc n).
Proof.
  intro n;
  rewrite <- StratProf_decomposition with (s:=dollarAcBc n);
  rewrite <- StratProf_decomposition with (s:=dollarAsBc n);
  simpl;
  rewrite gameNode; rewrite gameNode; apply gEqualNode;
  induction c; [apply refGEqual | apply sameGameBcAs_BcAc].
Qed.

(* SPE *)
Lemma SPEDolAcBs: forall n, SPE geDol (dollarAcBs n).
Proof.
  cofix SPEDolAcBs;
  intro n;
  decomp;
  apply SPENode with (c':=r)(u:=[n+1,n+1])(u':=[n+1,n+1]);
  [apply AlwaysNode; [apply ConvNode;apply ConvergentDolBsAc |
                      induction c'; [apply AlwaysLeaf | apply AlwsConvDolBsAc]] |
   apply UassignDolBsAc |
   apply UassignDolBsAc |
   solvegeDol |
   decomp; apply SPENode with (c':=r)(u:=[n+1,n+1])(u':=[n+1+1,n+1+1]);
   [apply AlwaysNode; [apply ConvNode;  apply ConvLeaf |
                       induction c'; [apply AlwaysLeaf| apply AlwsConvDolAcBs]] |
    apply UassignDolAcBs |
    apply UassignLeaf |
    solvegeDol |
   apply SPEDolAcBs]].
Qed.

Lemma SPEDolBsAc: forall n, SPE geDol (dollarBsAc n).
Proof.
  cofix SPEDolBsAc;
  intro n;
  decomp;
  apply SPENode with (c':=r)(u:=[n+1,n+1])(u':=[n+1+1,n+1+1]);
  [apply AlwaysNode; [apply ConvNode; apply ConvLeaf | induction c';[apply AlwaysLeaf | apply AlwsConvDolAcBs]] |
   apply UassignDolAcBs |
   apply UassignLeaf | 
   solvegeDol |
   apply SPEDolAcBs].
Qed.
 
Lemma SPEDolAsBc: forall n, SPE geDol (dollarAsBc n).
Proof.
  cofix SPEDolAsBc;
  intro n;
  decomp;
  apply SPENode with (c':=r)(u:=[n+1,n])(u':=[n+1+1,n+1]);
  [apply AlwaysNode; [apply ConvNode; apply ConvLeaf |
                      induction c';[apply AlwaysLeaf | apply AlwsConvDolBcAs]] |
   apply UassignDolBcAs |
   apply UassignLeaf | 
   solvegeDol |
   decomp; 
   apply SPENode with (c':=r)(u:=[n+1+1,n+1])(u':=[n+1+1,n+1]); 
   [apply AlwaysNode; [apply ConvNode; apply ConvergentDolAsBc |
                       induction c'; [apply AlwaysLeaf | apply AlwsConvDolAsBc]] |
    apply UassignDolAsBc |
    apply UassignDolAsBc |
    auto |
    apply SPEDolAsBc]] ;
  solvegeDol.
Qed.

Lemma SPEDolBcAs: forall n, SPE geDol (dollarBcAs n).
Proof.
  intro n; decomp; apply SPENode with (c':=r)(u:=[n+1+1,n+1])(u':=[n+1+1,n+1]);
  [apply AlwaysNode; [apply ConvNode; apply ConvergentDolAsBc |
                      induction c'; [apply AlwaysLeaf | apply AlwsConvDolAsBc]] |
   apply UassignDolAsBc |
   apply UassignDolAsBc |
   solvegeDol | 
   apply SPEDolAsBc].
Qed.

(* Good *)
Lemma GoodDolAcBc: forall n, good geDol (dollarAcBc n).
Proof.
  intro n;
  decomp;
  apply goodNode with (next':= <<[n+1,n]>> +++ dollarBcAs n);
   [rewrite gameNode; rewrite gameNode; apply gEqualNode;
   induction c; [ apply refGEqual | apply sameGameBcAs_BcAc]|
   apply SPENode with (c':=r)(u:=[n+1+1,n+1])(u':=[n+1+1,n+1]);
     [apply AlwaysNode; [apply ConvNode; apply ConvergentDolBcAs |
                         induction c'; [apply AlwaysLeaf |  apply AlwsConvDolBcAs]] |
      apply UassignDolBcAs | 
      apply UassignDolBcAs |
      auto |
      apply SPEDolBcAs]];
   solvegeDol.
Qed.

Lemma GoodDolBcAc: forall n, good geDol (dollarBcAc n).
Proof.
  intro n; decomp; decomp;
  apply goodNode with (next':= <<[n+1,n+1]>> +++ dollarAsBc (n + 1));
  [rewrite gameNode; rewrite gameNode; apply gEqualNode;
   induction c; [rewrite gameLeaf; apply gEqualLeaf| apply sameGameAcBc_AsBc] |
   apply SPENode with (c':=r)(u:=[n+1+1,n+1])(u':=[n+1+1,n+1]);
     [apply AlwaysNode; [apply ConvNode; apply ConvergentDolAsBc |
                         induction c'; [apply AlwaysLeaf | apply AlwsConvDolAsBc]] |
      apply UassignDolAsBc |
      apply UassignDolAsBc |
      auto |
      apply SPEDolAsBc]];
  solvegeDol.
Qed.

(* Along Good AcBc *)
Lemma AlongGoodDolAcBc: forall n, AlongGood geDol (dollarAcBc n).
Proof.
  cofix AlongGoodDolAcBc.
  intro n; decomp; apply AlongNode.
  replace (<< Alice, r, << [n+1, n] >> +++ dollarBcAc n >>) with (dollarAcBc n).
    apply GoodDolAcBc.
     rewrite <- StratProf_decomposition with (s:=dollarAcBc n); simpl; reflexivity.
  decomp.
  apply AlongNode.
  replace  (<< Bob, r, << [n+1,n+1] >> +++ dollarAcBc (n+1) >>)  with (dollarBcAc n).
  apply GoodDolBcAc.
 rewrite <- StratProf_decomposition with (s:=dollarBcAc n); simpl; reflexivity.
apply AlongGoodDolAcBc.
Qed.

(* Divergent *)
Lemma DivergenceDolAcBc: forall n, ↑ (dollarAcBc n).
Proof.
  cofix DivergenceDolAcBc; 
  intro n;
  decomp; apply divNode;
  decomp; apply divNode;
  apply DivergenceDolAcBc.
Qed.

End Dollar.