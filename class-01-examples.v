
(* Let's look at the following example: *)
Example ex1: forall A B: Prop, (A -> B) -> A -> B.
(* We want to prove, that for all propositions A and B if A implies B and A holds then B also holds.
   Now we step through the proof in Coq, which is a sequence of tactics, and comment every single line
   with its logical sense. Look at list of hypotheses and a subgoals. *) 
Proof. (* We start proof *)
  intro. (* Let's take some proposition A. *)
  intro. (* Let's take some proposition B. *)
  intro. (* To prove proposition (P -> Q) we usually assume P as a hypothesis and then prove Q. 
             So here we'll get hypothesis H: A -> B and the goal will be A -> B.
             In fact, here we can stop and apply this H to the goal, but we'll go further instead. *)
  intro. (* New hypothesis H0: A, goal: B. *)
  apply H. (* No we can apply hypothesis H, because it's conclusion is the same as our goal. 
              Applying H will also set its premise as a new goal. *)
  exact H0. (* Now goal coincides with one of hypotheses, namely H0, that allows us to use 'exact' tactic. *)
  (* No more goals, proof is completed, save it. *)
Qed.

(* This kind of reasoning is called 'backward reasoning, because we move from goals to the implications 
   in hypothesis and then to their premices.

   The same proof can be written shorter thanks to tactic 'intros':
 *)
Example ex11: forall A B: Prop, (A -> B) -> A -> B.
Proof.
  intros. (* Introduce all propositions and premises as hypotheses. *)
  apply H.
  assumption. (* Find one of assumptions which coincides with the goal and it. This is sometimes better
               than using particular name of hypothesis in 'exact'. *)
Qed.

Example ex12: forall A B: Prop, (A -> B) -> A -> B.
Proof.
  auto. (* Well, yeah, that's not fair, I know. But try to resist using this tactic until told so. *)
Qed.


(* Now we learn how to deal with disjunctions, conjunctions and negations, 
   how to prove them (in goals) and use them (in hypotheses). *)

Example ex2: forall A B: Prop, A -> A \/ B.
Proof.
  intros.
  left. (* To prove disjunction we have to specify which part in particular we want to prove. 
           Here we can prove left part. Beware, intuitionistic logic here! *)
  assumption.
Qed.

Example ex3: forall x y z: Prop, (x -> z) -> (y -> z) -> (x \/ y -> z).
Proof.
  intros. (* Look at hypotheses, the main question here is how to use disjunction in H1. 
             We have to 'destruct' it, that means exploring two cases: if x holds and if y holds.
             If disjunction in H1 holds then one of its parts is necessarily holds, but we don't
             know which one, so we do really have two cases. *)
  destruct H1. (* H1 becomes 'x', so x holds and we apply implication H. *)
    (* Note indentation here, this is way to mark visually proofs for subgoals arisen after 'destruct'. *)
    apply H. assumption. (* The first case is solved and we move to the second one. *)
    (* H1 becomes 'y', so y holds and we apply implication H0. *)
    apply H0. assumption.
Qed.

Example ex4: forall a b: Prop, a /\ b -> a.
Proof.
  intros.
  destruct H. (* Here we destruct conjunction so evidently we get two hypotheses for the same
                 goal, which are both parts of conjuction. *)
  assumption.
Qed.

Example ex5: forall a b: Prop, a -> b -> a /\ b.
Proof.
  intros. (* How to prove conjunction? Well, we have to prove both parts. *)
  split. (* We use 'split' to literally split conjunction into two parts. So we get two
            subgoals and have to prove them both independently. 
            Happily, the proof is straightforward, we just use assumptions in  both cases. *)
  assumption.
  assumption.
Qed.
  
(* If proofs for several cases are the same we can use 'tactical' ; (semicolon),
   as in example below. *)
Example ex51: forall a b: Prop, a -> b -> a /\ b.
Proof.
  intros.
  split; assumption. (* Tactic 'assumption' is executed for both subgoals arisen after 'split'. *)
Qed.

(* We use negation ~P in the following sense: if we assume P then we come to contradiction (we get False).
   So we can read (and use whenever we like) ~P as implication P->False. *)
Example ex6: forall A: Prop, A -> ~~A.
Proof.
  intros. (* Now we have ~~A in goals, according to our interpretation that means (~A->False), so use
             intro one more time. *)
  intro.  (* We can clearly see contradiction in hypotheses. To prove it we apply H0 (~A === A->False)
             and then provide exact assumption. *)
  apply H0. 
  exact H. 
  (* The last two steps are not necessary, we can use 'contradiction' tactic instead. The 'contradiction' 
     tactic tries to find hypotheses like 'P' and '~P' and finishes the proof if succeeding. *)
Qed.


(* Next example is one direction of De Morgan's Law (the other one can't be proved in intuitionistic logic
  without additional assumptions). To prove it we use plenty of destructions. 
  Note also use of ';' tactical. *)
Example ex7: forall A B , A \/ B -> ~ (~ A /\ ~ B ).
Proof.
  intros.
  intro.
  destruct H; destruct H0; contradiction.
Qed.  (* By the way, try to use 'auto' here. Does it work? *)

(* P is predicate in the following Lemma, it takes the value from set T and turns it into proposition. *)
Lemma ex8: forall (T: Set) ( P : T -> Prop ), (~ exists x , P x ) -> forall x , ~ P x .
Proof.
  intros.
  intro.
  apply H.
  exists x. (* We have to provide something to prove 'exists' in goal. Well, we have what we need 
               (namely, x: T) in the list of assumptions. *)
  assumption.
Qed.

(* The words Example, Lemma, Theorem or Fact are true synonyms. Use whatever you feel appropriate. *)