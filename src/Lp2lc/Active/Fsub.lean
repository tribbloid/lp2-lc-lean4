
namespace Lp2lc.Active.Fsub

-- Coq: Lp2lc_coq\Active\Fsub.v:430-436
theorem open_tt_rec_type_core (T : typ) (j : Nat) (V U : typ) (i : Nat) (h : i ≠ j) : type U → type (open_tt_rec j V T) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:438-445
theorem open_tt_rec_type (T U : typ) : type U → type (open_tt T U) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:447-454
theorem subst_tt_fresh (Z : String) (U T : typ) : Z ∉ fv_tt T → subst_tt Z U T = T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:456-464
theorem subst_tt_open_tt_rec (T1 T2 X P : typ) (n : Nat) : type P → subst_tt X P (open_tt_rec n T1 T2) = open_tt_rec n (subst_tt X P T1) (subst_tt X P T2) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:466-474
theorem subst_tt_open_tt (T1 T2 X P : typ) : type P → subst_tt X P (open_tt T1 T2) = open_tt (subst_tt X P T1) (subst_tt X P T2) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:476-484
theorem subst_tt_open_tt_var (X Y : String) (U T : typ) : Y ≠ X → type U → subst_tt X U (open_tt T (var (Nat.ofString Y))) = open_tt (subst_tt X U T) (var (Nat.ofString Y)) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:486-496
theorem subst_tt_intro (X : String) (T2 U : typ) : X ∉ fv_tt T2 → type U → open_tt (subst_tt X U T2) U = T2 := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:498-503
theorem open_te_rec_term_core (e : trm) (j : Nat) (u : trm) (i : Nat) (P : Prop) : term u → term (open_te_rec j u e) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:505-512
theorem open_te_rec_type_core (e : trm) (j : Nat) (Q : typ) (i : Nat) (P : Prop) : i ≠ j → type Q → type (open_te_rec j Q e) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:514-525
theorem open_te_rec_term (e : trm) (U : typ) : term e → type U → term (open_te e U) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:527-533
theorem subst_te_fresh (X : String) (U : typ) (e : trm) : X ∉ fv_te e → subst_te X U e = e := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:535-544
theorem subst_te_open_te (e : trm) (T X : String) (U : typ) : type U → subst_te X U (open_te e (var (Nat.ofString T))) = open_te (subst_te X U e) (subst_tt X U (var (Nat.ofString T))) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:546-554
theorem subst_te_open_te_var (X Y : String) (U : typ) (e : trm) : Y ≠ X → type U → subst_te X U (open_te e (var (Nat.ofString Y))) = open_te (subst_te X U e) (var (Nat.ofString Y)) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:556-566
theorem subst_te_intro (X : String) (U : typ) (e : trm) : X ∉ fv_te e → type U → open_te (subst_te X U e) U = e := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:568-574
theorem open_ee_rec_term_core (e : trm) (j : Nat) (v u : trm) (i : Nat) : i ≠ j → term u → term (open_ee_rec j v e) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:576-581
theorem open_ee_rec_type_core (e : trm) (j : Nat) (V : typ) (u : trm) (i : Nat) : term u → type (open_ee_rec j u e) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:583-593
theorem open_ee_rec_term (u e : trm) : term u → term e → term (open_ee e u) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:595-602
theorem subst_ee_fresh (x : String) (u e : trm) : x ∉ fv_ee e → subst_ee x u e = e := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:604-614
theorem subst_ee_open_ee (t1 t2 u : trm) (x : String) : term u → subst_ee x u (open_ee t1 t2) = open_ee (subst_ee x u t1) (subst_ee x u t2) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:616-624
theorem subst_ee_open_ee_var (x y : String) (u e : trm) : y ≠ x → term u → subst_ee x u (open_ee e (var (Nat.ofString y))) = open_ee (subst_ee x u e) (var (Nat.ofString y)) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:626-635
theorem subst_ee_intro (x : String) (u e : trm) : x ∉ fv_ee e → term u → open_ee (subst_ee x u e) u = e := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:637-645
theorem subst_te_open_ee_var (Z : String) (P : typ) (x : String) (e : trm) : term P → x ≠ Z → subst_te Z P (open_ee e (var (Nat.ofString x))) = open_ee (subst_te Z P e) (var (Nat.ofString x)) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:647-655
theorem subst_ee_open_te_var (z : String) (u : trm) (e : trm) (X : String) : term u → X ∉ fv_te e → subst_ee z u (open_te e (var (Nat.ofString X))) = open_te (subst_ee z u e) (var (Nat.ofString X)) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:657-663
theorem subst_tt_type (T : typ) (Z : String) (P : typ) : type T → type P → type (subst_tt Z P T) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:665-671
theorem subst_te_term (e : trm) (Z : String) (P : typ) : term e → type P → term (subst_te Z P e) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:673-688
theorem subst_ee_term (e1 : trm) (Z : String) (e2 : trm) : term e1 → term e2 → term (subst_ee Z e2 e1) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:690-696
theorem wft_type (E : env) (T : typ) : wft E T → type T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:698-711
theorem wft_weaken (G : env) (T : typ) (E F : env) : wft (E ++ G) T → okt F → wft (E ++ F ++ G) T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:713-728
theorem wft_narrow (V U T : typ) (F E : env) (X : String) : wft (E ++ (X, bind.sub U) :: F) V → sub E U T → wft (E ++ (X, bind.sub T) :: F) V := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:730-745
theorem wft_strengthen (E F : env) (x : String) (U T : typ) : wft (E ++ (x, bind.typ U) :: F) T → sub E U T → wft (E ++ F) T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:747-771
theorem wft_subst_tb (F Q E : env) (Z : String) (P T : typ) : wft (E ++ (Z, bind.typ P) :: F) Q → wft E P → wft (E ++ F) (subst_tt Z P Q) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:773-793
theorem wft_open (E : env) (U T1 T2 : typ) : wft E U → wft (E ++ ("_", bind.sub U) :: []) T1 → (∀ X, wft (E ++ (X, bind.sub U) :: []) T2) → wft E (open_tt T1 T2) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:795-803
theorem ok_from_okt (E : env) : okt E → List.Sorted (· < ·) (E.keys) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:805-822
theorem wft_from_env_has_sub (x : String) (U E : env) : List.lookup x E = some (bind.sub U) → wft E U := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:824-841
theorem wft_from_env_has_typ (x : String) (U E : env) : List.lookup x E = some (bind.typ U) → wft E U := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:843-850
theorem wft_from_okt_typ (x : String) (T : typ) (E : env) : okt E → List.lookup x E = some (bind.typ T) → wft E T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:852-861
theorem wft_from_okt_sub (x : String) (T : typ) (E : env) : okt E → List.lookup x E = some (bind.sub T) → wft E T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:863-880
theorem wft_weaken_right (T : typ) (E F : env) : wft E T → okt F → wft (E ++ F) T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:882-889
theorem okt_push_inv (E : env) (X : String) (B : bind) : okt ((X, B) :: E) → okt E ∧ X ∉ E.keys := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:891-898
theorem okt_push_sub_inv (E : env) (X : String) (T : typ) : okt ((X, bind.sub T) :: E) → okt E ∧ X ∉ E.keys := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:900-902
theorem okt_push_sub_type (E : env) (X : String) (T : typ) : okt ((X, bind.sub T) :: E) → wft E T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:904-911
theorem okt_push_typ_inv (E : env) (x : String) (T : typ) : okt ((x, bind.typ T) :: E) → okt E ∧ x ∉ E.keys := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:913-919
theorem okt_push_typ_type (E : env) (X : String) (T : typ) : okt ((X, bind.typ T) :: E) → wft E T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:921-936
theorem okt_narrow (V : typ) (E F : env) (U X : String) : okt (E ++ (X, bind.sub U) :: F) → sub E U V → okt (E ++ (X, bind.sub V) :: F) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:938-952
theorem okt_strengthen (x : String) (T : typ) (E F : env) : okt (E ++ (x, bind.typ T) :: F) → sub E U T → okt (E ++ F) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:954-977
theorem okt_subst_tb (Q : typ) (Z : String) (P : typ) (E F : env) : okt (E ++ (Z, bind.typ P) :: F) → wft E P → okt (E ++ F) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:979-987
theorem notin_fv_tt_open (Y X : String) (T : typ) : Y ∉ fv_tt T → open_tt T (var (Nat.ofString Y)) = T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:989-997
theorem notin_fv_wf (E : env) (X : String) (T : typ) : wft E T → X ∉ fv_tt T → wft (E ++ (X, bind.sub T) :: []) T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:999-1012
theorem map_subst_tb_id (G : env) (Z : String) (P : typ) : (∀ x, List.lookup x G = none) → wft G P → List.map (subst_tb Z P) G = G := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1014-1023
theorem sub_regular (E : env) (S T : typ) : sub E S T → wft E S ∧ wft E T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1025-1060
theorem typing_regular (E : env) (e : trm) (T : typ) : typing E e T → term e ∧ wft E T ∧ okt E := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1062-1068
theorem value_regular (t : trm) : value t → term t := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1070-1120
theorem red_regular (t t' : trm) : red t t' → term t ∧ term t' := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1122-1133
theorem sub_reflexivity (E : env) (T : typ) : wft E T → sub E T T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1135-1150
theorem sub_weakening (E F G : env) (S T : typ) : sub (E ++ G) S T → okt F → sub (E ++ F ++ G) S T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1152-1157
definition transitivity_on (Q : env → typ → typ → Prop) := ∀ E S T, Q E S T → Q E T S → Q E S S

-- Coq: Lp2lc_coq\Active\Fsub.v:1159-1181
theorem sub_narrowing_aux (Q : env → typ → typ → Prop) (F E : env) (Z : String) (P S T : typ) : (∀ E S T, sub E S T → Q E S T) → wft (E ++ (Z, bind.sub P) :: F) S → wft (E ++ (Z, bind.sub P) :: F) T → Q (E ++ (Z, bind.sub S) :: F) T S := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1183-1201
theorem sub_transitivity (Q : env → typ → typ → Prop) : (∀ E S T, sub E S T → Q E S T) → transitivity_on Q := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1203-1216
theorem sub_narrowing (Q E F : env) (Z : String) (P S T : typ) : sub (E ++ (Z, bind.sub P) :: F) S T → sub E P S → sub (E ++ (Z, bind.sub T) :: F) S T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1218-1252
theorem sub_through_subst_tt (Q E F : env) (Z S T P : typ) : wft (E ++ (Z, bind.typ P) :: F) S → wft (E ++ (Z, bind.typ P) :: F) T → wft E P → sub (E ++ F) (subst_tt Z P S) (subst_tt Z P T) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1254-1271
theorem typing_weakening (E F G : env) (e : trm) (T : typ) : typing (E ++ G) e T → okt F → typing (E ++ F ++ G) e T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1273-1286
theorem sub_strengthening (x : String) (U E F S T : typ) : sub (E ++ (x, bind.typ U) :: F) S T → sub E U S → sub (E ++ F) S T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1288-1304
theorem typing_narrowing (Q E F : env) (X : String) (P e T : typ) : typing (E ++ (X, bind.sub P) :: F) e T → sub E P Q → typing (E ++ (X, bind.sub Q) :: F) e T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1306-1327
theorem typing_through_subst_ee (U E F : env) (x T e u : trm) : typing (E ++ (x, bind.typ U) :: F) e T → typing E u U → typing (E ++ F) (subst_ee x u e) T := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1329-1357
theorem typing_through_subst_te (Q E F : env) (Z e T P : typ) : typing (E ++ (Z, bind.typ P) :: F) e T → wft E P → typing (E ++ F) (subst_te Z P e) (subst_tt Z P T) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1359-1369
theorem typing_inv_abs (E : env) (S1 e1 : trm) (T : typ) : typing E (abs S1 e1) T → ∃ T2, T = arr S1 T2 ∧ (∀ x, typing ((x, bind.typ S1) :: E) e1 T2) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1371-1389
theorem typing_inv_tabs (E : env) (S1 e1 : trm) (T : typ) : typing E (tabs S1 e1) T → ∃ T2, T = all S1 T2 ∧ (∀ X, typing ((X, bind.sub S1) :: E) e1 T2) := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1391-1424
theorem preservation_result : preservation := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1426-1437
theorem canonical_form_abs (t U1 U2 : typ) : value t → typing [] t (arr U1 U2) → ∃ e, t = abs U1 e := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1439-1453
theorem canonical_form_tabs (t U1 U2 : typ) : value t → typing [] t (all U1 U2) → ∃ e, t = tabs U1 e := by sorry

-- Coq: Lp2lc_coq\Active\Fsub.v:1455-1455
theorem progress_result : progress := by sorry

import Lp2lc.Active.Fsub.Def
import Lp2lc.Active.FsubL_alt.Def
import Lp2lc.Active.Dsub.Def
import Lp2lc.Active.Dsubsup.Def
import Lp2lc.Active.Ddia.Def

set_option autoImplicit true

open scoped Classical
