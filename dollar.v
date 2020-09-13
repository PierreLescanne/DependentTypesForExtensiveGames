(* Time-stamp: "2018-02-08 18:19:03 pierre" *)
(****************************************************************)
(*                        dollar.v                              *)
(*                                                              *)
(**          © Pierre Lescanne  (December 2015)                 *)
(*                                                              *)
(*              LIP (ENS-Lyon, CNRS, INRIA)                     *)
(*                                                              *)
(*                                                              *)
(*  Developed in  V8.4pl4               January -- May   2016   *)
(****************************************************************)
Section Dollar.

Require Import games_Choice_Dependent.
Require Import Omega.

(* Setting sets for agents and choices *)
Inductive AliceBob : Set := | Alice | Bob.
Inductive DorR : Set := | d | r.
Definition Choice: AliceBob -> Set := fun a => DorR.

Arguments StratProf {Agent Utility Choice}.
Arguments Game {Agent Utility Choice}.
Arguments UAssignment [Agent Utility Choice] s H a.
Arguments game [Agent Utility Choice] s.
Arguments StratProf_decomposition [Agent Utility Choice] s.
Arguments Convergent [Agent Utility Choice] s.
Arguments AlwaysConvergent [Agent Utility Choice] s.
Arguments convLeaf [Agent Utility Choice] f.
Arguments convNode [Agent Utility Choice] a c next _.
Arguments StratProf_identity [Agent Utility Choice] s.
Arguments SPE [Agent Utility Choice] preference  s.
Arguments Uassign [Agent Utility Choice] s a u.
Arguments good [Agent Utility Choice] preference s.
Arguments gEqual [Agent Utility Choice] g1 g2.
Arguments Divergent  [Agent Utility Choice] s.
Arguments AlwaysGood  [Agent Utility Choice] preference s.

Notation "<< f >>" := (sLeaf AliceBob nat Choice f).
Notation "<< a , c , next >>" := 
  (sNode AliceBob nat Choice a c next).
Notation "[ x , y ]" := 
  (fun a:AliceBob => match a with Alice => x | Bob => y end).
Notation "<| f |>" := (gLeaf  AliceBob nat Choice f).
Notation "<| a , next |>" := (gNode AliceBob nat Choice a next).

Notation "s1 +++ s2" := 
  (fun c:DorR => match c with d => s1 | r => s2 end) 
  (at level 30).
Notation "↓ s " := (Convergent s) (at level 5).
Notation "⇓ s" := (AlwaysConvergent s)
                    (at level 15).
Notation "↑ s " := (Divergent s) (at level 5).
Notation "g == g'" := (gEqual g g') (at level 80).

Ltac decomp := rewrite <- StratProf_decomposition;  simpl.

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

Lemma UassignDolAcBsA: forall n, Uassign (dollarAcBs n) Alice (n+1).
Proof.
  intro n.
  rewrite <- StratProf_decomposition with (s:=dollarAcBs n); simpl.
  rewrite <- StratProf_decomposition with (s:=dollarBsAc n); simpl.
  apply UassignNode.
  apply UassignNode.
  apply UassignLeaf.  
Qed.

Lemma UassignDolAcBsB: forall n, Uassign (dollarAcBs n) Bob (n+1).
Proof.
  intro n.
  rewrite <- StratProf_decomposition with (s:=dollarAcBs n); simpl.
  apply UassignNode.
  rewrite <- StratProf_decomposition with (s:=dollarBsAc n); simpl.
  apply UassignNode.
  apply UassignLeaf.  
Qed.

Lemma UassignDolBsAcA: forall n, Uassign (dollarBsAc n) Alice (n+1).
Proof.
  intro n.
  rewrite <- StratProf_decomposition with (s:=dollarBsAc n); simpl.
  apply UassignNode.
  apply UassignLeaf.  
Qed.

Lemma UassignDolBsAcB: forall n, Uassign (dollarBsAc n) Bob (n+1).
Proof.
  intro n.
  rewrite <- StratProf_decomposition with (s:=dollarBsAc n); simpl.
  apply UassignNode.
  apply UassignLeaf.  
Qed.

(* A stops Bob continues *)
Lemma UassignDolAsBcA: forall n, Uassign (dollarAsBc n) Alice (n+1).
Proof.
  intro n.
  rewrite <- StratProf_decomposition with (s:=dollarAsBc n); simpl.
  apply UassignNode.
  apply UassignLeaf.  
Qed.

Lemma UassignDolAsBcB: forall n, Uassign (dollarAsBc n) Bob n.
Proof.
  intro n.
  rewrite <- StratProf_decomposition with (s:=dollarAsBc n); simpl.
  apply UassignNode.
  apply UassignLeaf.  
Qed.

Lemma UassignDolBcAsA: forall n, Uassign (dollarBcAs n) Alice (n+1+1).
Proof.
  intro n.
  rewrite <- StratProf_decomposition with (s:=dollarBcAs n); simpl.
  apply UassignNode.
  apply UassignDolAsBcA.  
Qed.

Lemma UassignDolBcAsB: forall n, Uassign (dollarBcAs n) Bob (n+1).
Proof.
  intro n.
  rewrite <- StratProf_decomposition with (s:=dollarBcAs n); simpl.
  apply UassignNode.
  apply UassignDolAsBcB.
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
Lemma SPEDolAcBs: forall n, SPE ge (dollarAcBs n).
Proof.
  cofix SPEDolAcBs;
  intro n;
  decomp;
  apply SPENode with (c':=r)(u:=n+1)(u':=n+1);
  [apply AlwaysNode; [apply ConvNode;apply ConvergentDolBsAc | induction c'; [apply AlwaysLeaf | apply AlwsConvDolBsAc]] |
   apply UassignDolBsAcA |
   apply UassignDolBsAcA | 
   auto | 
   decomp;
   apply SPENode with (c':=r)(u:=n+1)(u':=n+1+1);
   [apply AlwaysNode; [apply ConvNode;  apply ConvLeaf | induction c'; [apply AlwaysLeaf| apply AlwsConvDolAcBs]] |
    apply UassignDolAcBsB |
    apply UassignLeaf |
    omega |
    apply SPEDolAcBs]].
Qed.

Lemma SPEDolBsAc: forall n, SPE ge (dollarBsAc n).
Proof.
  cofix SPEDolBsAc;
  intro n;
  decomp;
  apply SPENode with (c':=r)(u:=n+1)(u':=n+1+1);
  [apply AlwaysNode; [apply ConvNode; apply ConvLeaf | induction c';[apply AlwaysLeaf | apply AlwsConvDolAcBs]] |
   apply UassignDolAcBsB |
   apply UassignLeaf | 
   omega |
   apply SPEDolAcBs].
Qed.
 
Lemma SPEDolAsBc: forall n, SPE ge (dollarAsBc n).
Proof.
  cofix SPEDolAsBc;
  intro n;
  decomp;
  apply SPENode with (c':=r)(u:=n+1)(u':=n+1+1);
  [apply AlwaysNode; [apply ConvNode; apply ConvLeaf |
                      induction c';[apply AlwaysLeaf | apply AlwsConvDolBcAs]] |
   apply UassignDolBcAsA |
   apply UassignLeaf | 
   omega |
   decomp; 
   apply SPENode with (c':=r)(u:=n+1)(u':=n+1); 
   [apply AlwaysNode; [apply ConvNode; apply ConvergentDolAsBc |
                       induction c'; [apply AlwaysLeaf | apply AlwsConvDolAsBc]] |
    apply UassignDolAsBcB |
    apply UassignDolAsBcB |
    auto |
    apply SPEDolAsBc]].
Qed.

Lemma SPEDolBcAs: forall n, SPE ge (dollarBcAs n).
Proof.
  intro n; decomp; apply SPENode with (c':=r)(u:=n+1)(u':=n+1);
  [apply AlwaysNode; [apply ConvNode; apply ConvergentDolAsBc |
                      induction c'; [apply AlwaysLeaf | apply AlwsConvDolAsBc]] |
   apply UassignDolAsBcB |
   apply UassignDolAsBcB |
   auto | 
   apply SPEDolAsBc].
Qed.

(* Good *)
Lemma GoodDolAcBc: forall n, good ge (dollarAcBc n).
Proof.
  intro n;
  decomp;
  apply goodNode with (next':= <<[n+1,n]>> +++ dollarBcAs n);
  split;
  [rewrite gameNode; rewrite gameNode; apply gEqualNode;
   induction c; [ apply refGEqual | apply sameGameBcAs_BcAc]|
   apply SPENode with (c':=r)(u:=n+1+1)(u':=n+1+1);
     [apply AlwaysNode; [apply ConvNode; apply ConvergentDolBcAs |
                         induction c'; [apply AlwaysLeaf |  apply AlwsConvDolBcAs]] |
      apply UassignDolBcAsA | 
      apply UassignDolBcAsA |
      auto |
      apply SPEDolBcAs]].
Qed.

Lemma GoodDolBcAc: forall n, good ge (dollarBcAc n).
Proof.
  intro n; decomp; decomp;
  apply goodNode with (next':= <<[n+1,n+1]>> +++ dollarAsBc (n + 1));
  split;
  [rewrite gameNode; rewrite gameNode; apply gEqualNode;
   induction c; [rewrite gameLeaf; apply gEqualLeaf| apply sameGameAcBc_AsBc] |
   apply SPENode with (c':=r)(u:=n+1)(u':=n+1);
     [apply AlwaysNode; [apply ConvNode; apply ConvergentDolAsBc |
                         induction c'; [apply AlwaysLeaf | apply AlwsConvDolAsBc]] |
      apply UassignDolAsBcB |
      apply UassignDolAsBcB |
      auto |
      apply SPEDolAsBc]].
Qed.

(* Always Good AcBc *)
Lemma AlwaysGoodDolAcBc: forall n, AlwaysGood ge (dollarAcBc n).
Proof.
  cofix AlwaysGoodDolAcBc; 
  intro n; decomp; apply AlwaysNode;
  [replace (<< Alice, r, << [n+1, n] >> +++ dollarBcAc n >>) with (dollarAcBc n);
    [apply GoodDolAcBc | rewrite <- StratProf_decomposition with (s:=dollarAcBc n); simpl; reflexivity]|
    induction c';
    [apply AlwaysLeaf | 
     decomp; apply AlwaysNode;
     [replace (<< Bob, r, << [n+1, n+1] >> +++ dollarAcBc (n + 1)>>) with (dollarBcAc n);
       [apply GoodDolBcAc | rewrite <- StratProf_decomposition with (s:=dollarBcAc n);  simpl; reflexivity]|
      induction c'; [ apply AlwaysLeaf | apply AlwaysGoodDolAcBc]]]].
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
