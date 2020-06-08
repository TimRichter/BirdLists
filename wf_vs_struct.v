
(* # Wohlfundierte vs. strukturelle Induktion *)

(* Wir könnten die Funktionen auch in Coq per Pattern Matching
   definieren, aber hier wird als Ergänzung zum bereits
   besprochenenen Agda-Beweis der Beweismodus benutzt. *)

(* Dabei wird der Beweis interaktiv entwickelt mit Hilfe von
   *Taktiken*, die (grob gesagt) Anwendung logischer Inferenzregeln 
   kapseln. *)

(* Die Beweis-Skripte können auch ohne lokale Installation von Coq
   online unter

   https://jscoq.github.io/node_modules/jscoq/examples/scratchpad.html

   ausprobiert werden... einfach per copy/paste einfügen
   Man kann dann mit den grünen Pfeil-Tasten schrittweise
   durch die Beweise gehen. (Am Anfang dauert es einen Moment
   bis die Bibliotheken geladen sind.)

   Die Startseite des JSCoq-Projekts ist zu finden unter:

   https://x80.org/rhino-coq/        *)

Require Import Arith.

(* Wohlfundierte Induktion => Strukturelle Induktion *)

Lemma wf_impl_struct :

  (forall (P:nat -> Prop), 
    (forall n, (forall m, m < n -> P m) -> P n) -> forall n, P n) 
   -> 
  (forall P : nat -> Prop,
     P 0 -> (forall n : nat, P n -> P (S n)) -> forall n : nat, P n).

Proof.

  intros wf_ip P p_zero p_step k.
  apply wf_ip.

  intros n all_smaller_P.

  (* Fallunterscheidung: n = 0 oder n = S n' für ein n' : nat *)
  case_eq n.

  - intro n_eq_zero.
    exact p_zero.

  - intros n' n_eq_Sn'.
    rewrite n_eq_Sn' in all_smaller_P.

    Print Nat.lt_succ_diag_r.

    pose (Nat.lt_succ_diag_r n') as n'_lt_Sn'.
    pose (all_smaller_P n' n'_lt_Sn') as P_n'.
    pose (p_step n' P_n') as P_Sn'.

    exact P_Sn'.

Qed.


Print wf_impl_struct.


(* Für die andere Richtung brauchen wir noch ein Lemma: *)

Lemma dec_le : 

  forall m n : nat, m <= n -> m = n \/ m < n.

Proof.

intros.
induction H.

- left.
  reflexivity.

- case IHle.

  + intro m_eq_m0.
    right.

    rewrite m_eq_m0.
    apply Nat.lt_succ_diag_r.

  + intro m_lt_m0.
    right.

    apply Nat.lt_lt_succ_r in m_lt_m0 as m_lt_sm0.
    exact m_lt_sm0.

Qed.

(* Strukturelle Induktion => Wohlfundierte Induktion *)

Lemma struct_impl_wf :

  (forall P : nat -> Prop,
     P 0 ->
     (forall n : nat, P n -> P (S n)) ->
     forall n : nat, P n)
   ->
     (forall (Q:nat -> Prop), (forall n, (forall m, m < n -> Q m) -> Q n) 
      -> forall n, Q n).

Proof.

intros stip Q wf_step k.

pose (fun n : nat => forall m : nat, m < n -> Q m) as P.
assert (P 0) as P_0.

- unfold P.
  intros m m_lt_0.

  inversion m_lt_0.

- assert (forall n : nat, P n -> P (S n)) as p_step.

  + intros n P_n.
    unfold P; unfold P in P_n.
    intros m m_lt_sn.

    apply Arith.Lt.lt_n_Sm_le in m_lt_sn.
    apply dec_le in m_lt_sn as meqn_or_mltn.

    case meqn_or_mltn.

      { intro m_eq_n.
        rewrite m_eq_n.
        pose (wf_step n P_n) as Q_n.
        exact Q_n.
       }

      { intro m_lt_n.
        pose (P_n m m_lt_n) as Q_m.
        exact Q_m.
      }

  + pose (stip P P_0 p_step k) as P_k.
    pose (wf_step k P_k) as Q_k.
    exact Q_k.

Qed.

Print struct_impl_wf.



