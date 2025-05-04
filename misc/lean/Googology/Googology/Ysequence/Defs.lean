import Googology.YSequence.Diagonal
import Mathlib.Data.List.Intervals

namespace Ysequence

section Copy

def ascends {x : Mountain} (h : x.IsLimit) (i : Index x.values.val) : Prop :=
  findIterateOfToNoneOrLtId
    (f := inIndexElim
      (fun p => inIndexElim (s := p.get) Index.get none ((badroot ..).get h.badroot_isSome).val.snd)
      none)
    (by
      apply toNoneOrLtId_inIndexElim_val_none_of_forall_index
      intro p
      unfold inIndexElim
      split_ifs
      · exact h.to_isCoherent.to_isCrossCoherent.to_parent_isCoherent.get_lt ⟨p, _⟩
      · exact WithBot.bot_lt_coe _)
    (instDecidableEqNat ((badroot ..).get h.badroot_isSome).val.fst)
    i.val |>.isSome

instance {x : Mountain} (h : x.IsLimit) : DecidablePred <| ascends h :=
  fun _ => decEq ..

lemma ascends_badroot {x : Mountain} (h : x.IsLimit) :
    ascends h ((badroot ..).get h.badroot_isSome).fst :=
  (findIterate_isSome_iff ..).mpr ⟨0, rfl, rfl⟩

lemma ascends_mountain_last {x : ValueParentListPair} (h : (buildMountain x).IsLimit) :
    ascends h (Index.last h.to_values_val_ne_nil) :=
  by
  apply (findIterate_isSome_iff ..).mpr
  simp only [Set.mem_def]
  conv in ∃ _, _ = _ => rw [exists_congr fun _ => Eq.comm, ← Option.eq_some_iff_get_eq]
  suffices ∀ j ≤ _, ∃ k,
      (flip bind (inIndexElim (fun p => inIndexElim (s := p.get) Index.get _ j) none))^[k] _ = _
    from this ((badroot ..).get h.badroot_isSome).val.snd (Nat.le_refl _)
  conv in inIndexElim Index.get _ _ =>
    conv in Index.get => change (Index₂.get ⟨p, ·⟩)
    simp only [mountain_parent_at_index_eq_parent, Index₂.mk_val_snd]
    rw [show inIndexElim .. = parent x _ j
        by
        unfold inIndexElim
        split_ifs with h
        · rfl
        · rw [(buildMountain x).pairable.symm.snd, mountain_height_eq,
            ← value_isSome_iff_lt_height, Option.not_isSome_iff_eq_none] at h
          exact Eq.symm <| parent_of_value_eq_none h]
  generalize_proofs _ _ hr heq
  conv in inIndexElim _ _ =>
    rw [show inIndexElim _ _ = inIndexElim (parent x · j) _
        by
        unfold inIndexElim
        funext
        exact dite_congr (congrArg _ heq) (congrFun rfl) (congrFun rfl)]
  rw [Index.last_val, (buildMountain x).pairable.fst, heq]
  obtain ⟨k, hk⟩ := exists_iterate_descend_last_last_eq_badroot h.to_values_val_ne_nil h.to_isCoherent
  suffices ∀ (p : Option (Index₂ _)) hp (p_eq : _ = p), ∀ j ≤ (p.get hp).val.snd, ∃ k, ((flip bind (inIndexElim (parent x · j) _))^[k] <| some _) = some (p.get hp).val.fst from this _ (h.badroot_isSome) hk
  clear hk
  intro p hp p_eq j hj
  subst p_eq
  rw [Option.get_map, Pairable₂.val_transfer] at hj ⊢
  induction k with
  | zero => exact ⟨0, by dsimp; congr 2; symm; apply mountain_length_eq⟩
  | succ k IH =>
    have hp' := iterate_bind_isSome_le (Nat.le_succ k) (Option.isSome_map' .. ▸ hp)
    set p := _^[k + 1] _ with p_eq
    change ∃ k, _ = some (p.get _).val.fst
    rw [Function.iterate_succ_apply', ← Option.some_get hp'] at p_eq
    simp only [flip, Option.bind_eq_bind] at p_eq
    rw [Option.some_bind] at p_eq
    specialize IH (Option.isSome_map' .. |>.symm ▸ hp') (hj.trans ?_)
    · conv in _^[k + 1] _ => change p; rw [p_eq]
      exact (descend_pairwise_le_of_it_isSome ..).right
    rcases IH with ⟨k₁, hk₁⟩
    set p' := _^[k] _ with p'_eq
    change _ = some (p'.get _).val.fst at hk₁
    change _ = descend _ (p'.get _) at p_eq
    refine Exists.casesOn ?_ fun k' hk' => ⟨k' + k₁, hk'⟩
    simp_rw [p_eq]
    simp only [Function.iterate_add_apply, hk₁]
    dsimp only [descend]
    split_ifs
    · simp only [Option.get_some, Option.some_get,
        ParentMountain.IsCoherent.indexParentOfIsSome_val, mountain_parent_at_index_eq_parent]
      convert exists_iterate_parent_eq_parent_upwards _ _
      · rfl
      · refine le_trans (le_of_le_of_eq hj ?_)
          (descend_pairwise_le_of_it_isSome (Option.isSome_map' .. ▸ p_eq ▸ hp)).right
        simp_rw [Function.iterate_succ_apply', ← p'_eq]
        conv in flip .. =>
          rw [← Option.some_get hp']
          simp only [flip, Option.bind_eq_bind, Option.some_bind, Option.map_some']
    · use 0
      simp only [Option.bind_eq_bind, ne_eq, Function.iterate_zero_apply, Option.some.injEq]
      generalize_proofs _ _ hp
      rw [
        ← Option.get_map (f := Index₂.val)
          (h := Option.isSome_map' .. |>.symm ▸ hp'),
        ← Option.get_map (f := Prod.fst)
          (h := Option.isSome_map' .. |>.symm ▸ Option.isSome_map' .. |>.symm ▸ hp'),
        ← Option.get_map (f := Index₂.val)
          (h := Option.isSome_map' .. |>.symm ▸ hp),
        ← Option.get_map (f := Prod.fst)
          (h := Option.isSome_map' .. |>.symm ▸ Option.isSome_map' .. |>.symm ▸ hp)]
      congr 1
      match p'_val : (p'.get hp').snd with
      | ⟨0, _⟩ =>
        rw [p'_val] at hp
        contradiction
      | ⟨j + 1, _⟩ =>
        simp only [Option.map_map, Option.map_some', Index₂.mk_val_fst, Index₂.fst_val,
          Option.map_eq_some', Function.comp_apply]
        exact ⟨_, ⟨Option.some_get _ |>.symm, rfl⟩⟩

theorem not_ascends_of_lt_badroot {x : Mountain} (h : x.IsLimit) {i : Index x.values.val}
    (hi : i < ((badroot ..).get h.badroot_isSome).fst) : ¬ascends h i :=
  by
  unfold ascends
  generalize_proofs
  rw [Option.not_isSome_iff_eq_none, findIterateOfToNoneOrLtId, findIterate_eq_none_iff]
  intro k hk
  cases k with
  | zero => exact ne_of_gt hi
  | succ k =>
    refine ne_of_gt (lt_trans ?_ hi)
    rw [← WithBot.coe_lt_coe, ← WithBot.some_eq_coe, Option.some_get]
    apply toNoneOrLtId_iterate_succ
    assumption

theorem ge_badroot_of_ascends {x : Mountain} (h : x.IsLimit) {i : Index x.values.val}
    (hi : ascends h i) : i ≥ ((badroot ..).get h.badroot_isSome).fst :=
  Nat.ge_of_not_lt <| mt (not_ascends_of_lt_badroot h) (not_not_intro hi)

theorem height_gt_badroot_val_snd_add_one_of_ascends_of_fst_ne_badroot_fst {x : Mountain}
    (h : x.IsLimit) {i : Index x.values.val} (h_ascends : ascends h i)
    (hir : i ≠ ((badroot ..).get h.badroot_isSome).fst) :
    ((badroot ..).get h.badroot_isSome).val.snd + 1 < i.get.length :=
  by
  obtain ⟨k, hk₁, hk₂⟩ := (findIterate_isSome_iff ..).mp h_ascends
  apply iterate_bind_isSome_le at hk₁
  case hmn =>
    rw [Nat.one_le_iff_ne_zero]
    intro H
    simp only [H, Function.iterate_zero_apply] at hk₂
    rw [Option.get_some, Set.mem_def, ← Index₂.fst_val] at hk₂
    apply Fin.ext at hk₂
    symm at hk₂
    contradiction
  rw [Function.iterate_one, flip, Option.bind_eq_bind, Option.some_bind,
    inIndexElim_of_lt (hi := Nat.lt_of_lt_of_eq i.isLt x.pairable.fst), inIndexElim] at hk₁
  split_ifs at hk₁ with hr
  case neg => contradiction
  change Index₂.get ⟨_, _⟩ |> Option.isSome at hk₁
  rw [h.to_isCoherent.to_isCrossCoherent.to_parent_isCoherent.get_isSome_iff] at hk₁
  dsimp only [Index₂.val_mk_mk] at hk₁
  rw [(x.pairable.symm.snd _).def, Pairable.transfer, Fin.mk_val] at hk₁ hr
  change Fin.val ⟨_, hr⟩ ≠ _ at hk₁
  rw [Index.val_ne_pred_length_iff] at hk₁
  exact Nat.add_lt_of_lt_sub hk₁

theorem height_gt_badroot_val_snd_of_ascends {x : Mountain} (h : x.IsLimit) {i : Index x.values.val} (h_ascends : ascends h i) : ((badroot ..).get h.badroot_isSome).val.snd < i.get.length :=
  if h_isbr : i = ((badroot ..).get h.badroot_isSome).fst
  then h_isbr ▸ ((badroot ..).get h.badroot_isSome).val_snd_lt
  else
    Nat.lt_of_succ_lt <|
      height_gt_badroot_val_snd_add_one_of_ascends_of_fst_ne_badroot_fst h h_ascends h_isbr

def copyParent {x : Mountain} (h : x.IsLimit) (i : Index₂ x.parents.val) (k : ℕ) : Option ℕ :=
  i.get.map fun p =>
    let r := ((badroot ..).get h.badroot_isSome).val.fst
    if p ≥ r then p + (x.values.val.length - 1 - r) * k else p

@[simp]
lemma copyParent_isSome {x : Mountain} (h : x.IsLimit) (i : Index₂ x.parents.val) (k : ℕ) :
    (copyParent h i k).isSome = i.get.isSome :=
  Option.isSome_map' ..

theorem copyParent_get_le_new_position_of_isSome {x : Mountain} (h : x.IsLimit)
    (i : Index₂ x.parents.val) (k : ℕ) (hp : (copyParent h i k).isSome) :
    let p := i.get.get (copyParent_isSome .. ▸ hp)
    let r := ((badroot ..).get h.badroot_isSome).val.fst
    (copyParent h i k).get hp ≤ p + (x.values.val.length - 1 - r) * k :=
  by
  simp only [copyParent, Option.get_map]
  split_ifs
  · apply Nat.le_refl
  · apply Nat.le_add_right

lemma copyParent_get_lt_new_length_of_isSome {x : Mountain} (h : x.IsLimit)
    (i : Index₂ x.parents.val) (k : ℕ) (hp : (copyParent h i k).isSome) :
    let r := ((badroot ..).get h.badroot_isSome).val.fst
    (copyParent h i k).get hp < i.val.fst + (x.values.val.length - 1 - r) * k :=
  by
  refine Nat.lt_of_le_of_lt (copyParent_get_le_new_position_of_isSome ..) (Nat.add_lt_add_right ?_ _)
  rw [← WithBot.coe_lt_coe, ← WithBot.some_eq_coe, Option.some_get]
  exact h.to_isCoherent.to_isCrossCoherent.to_parent_isCoherent.get_lt i

def finIco {k : ℕ} (m n : Fin (k + 1)) : List (Fin k) :=
  (List.Ico m n).pmap Fin.mk fun _ h =>
    Nat.lt_of_lt_of_le (List.Ico.mem.mp h).right (Nat.le_of_lt_succ n.isLt)

def copySeam {x : Mountain} (h : x.IsLimit) (i : Index x.values.val) (k : ℕ+) : List (Option ℕ) :=
  if h_isbr : i = ((badroot ..).get h.badroot_isSome).fst
  then
    if h_surface : surfaceAt (Index.last h.to_values_val_ne_nil) = 1
    then
      (finIco
          0
          ⟨((badroot ..).get h.badroot_isSome).val.snd,
            by
            apply Nat.lt_of_le_of_lt (badroot_val_snd_le_cutChild_val_of_isLimit h)
            rw [cutChild, ite_cond_eq_true _ _ (eq_true h_surface), Fin.val_mk,
              (x.pairable.snd _).def]
            exact Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.lt_succ_self _)⟩ |>.map
        fun j => copyParent h ⟨x.pairable.fst.transfer (Index.last h.to_values_val_ne_nil), j⟩ k.natPred) ++
      (finIco
          ⟨((badroot ..).get h.badroot_isSome).val.snd,
            by
            rw [h_isbr, ← (x.pairable.snd _).def]
            exact (Index₂.val_snd_lt _).trans (Nat.lt_succ_self _)⟩
          (Fin.last _) |>.map
        fun j => copyParent h ⟨x.pairable.fst.transfer i, j⟩ k.val)
    else
      (finIco
          0
          ⟨((badroot ..).get h.badroot_isSome).val.snd,
            by
            apply Nat.lt_of_le_of_lt (badroot_val_snd_le_cutChild_val_of_isLimit h)
            rw [cutChild, ite_cond_eq_false _ _ (eq_false h_surface), Index.last_val,
              (x.pairable.snd _).def]
            exact Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.lt_succ_self _)⟩ |>.map
        fun j => copyParent h ⟨x.pairable.fst.transfer (Index.last h.to_values_val_ne_nil), j⟩ k.natPred) ++
      (List.replicate
        (((cutChild h.to_values_val_ne_nil).val - ((badroot ..).get h.badroot_isSome).val.snd) *
          k.natPred)
        (copyParent h
          ⟨x.pairable.fst.transfer (Index.last h.to_values_val_ne_nil),
            ⟨((badroot ..).get h.badroot_isSome).val.snd,
              by
              apply Nat.lt_of_le_of_lt (badroot_val_snd_le_cutChild_val_of_isLimit h)
              rw [cutChild, ite_cond_eq_false _ _ (eq_false h_surface), Index.last_val,
                (x.pairable.snd _).def]
              exact Nat.sub_lt (List.length_pos_of_ne_nil (x.parents.index_get_ne_nil _))
                Nat.zero_lt_one⟩⟩
          k.natPred)) ++
      (finIco
          ⟨((badroot ..).get h.badroot_isSome).val.snd,
            by
            apply Nat.lt_of_le_of_lt (badroot_val_snd_le_cutChild_val_of_isLimit h)
            rw [cutChild, ite_cond_eq_false _ _ (eq_false h_surface), Index.last_val,
              (x.pairable.snd _).def]
            exact Nat.lt_of_le_of_lt (Nat.sub_le ..) (Nat.lt_succ_self _)⟩
          (Fin.last _) |>.map
        fun j => copyParent h ⟨x.pairable.fst.transfer (Index.last h.to_values_val_ne_nil), j⟩ k.natPred)
  else
    (finIco
        0
        ⟨min ((badroot ..).get h.badroot_isSome).val.snd i.get.length,
          Nat.lt_succ_of_le <| (x.pairable.snd _).def ▸ min_le_right ..⟩ |>.map
      fun j => copyParent h ⟨x.pairable.fst.transfer i, j⟩ k.val) ++
    (if h_ascends : ascends h i
      then
        List.replicate
          (((cutChild h.to_values_val_ne_nil).val - ((badroot ..).get h.badroot_isSome).val.snd) *
            k.val)
          (copyParent h
            ⟨x.pairable.fst.transfer i,
              ⟨((badroot ..).get h.badroot_isSome).val.snd,
                (x.pairable.snd _).def ▸ height_gt_badroot_val_snd_of_ascends h h_ascends⟩⟩
            k.val)
      else []) ++
    (finIco
        ⟨min ((badroot ..).get h.badroot_isSome).val.snd i.get.length,
          Nat.lt_succ_of_le <| (x.pairable.snd _).def ▸ min_le_right ..⟩
        (Fin.last _) |>.map
      fun j => copyParent h ⟨x.pairable.fst.transfer i, j⟩ k.val)

theorem copySeam_length {x : Mountain} (h : x.IsLimit) (i : Index x.values.val) (k : ℕ+) :
    (copySeam h i k).length =
      if surfaceAt (Index.last h.to_values_val_ne_nil) ≠ 1 ∧ ascends h i
      then
        i.get.length +
          ((cutChild h.to_values_val_ne_nil).val - ((badroot ..).get h.badroot_isSome).val.snd) *
            k.val
      else i.get.length :=
  by
  rw [copySeam]
  split_ifs with h_isbr h_surface hi hi h_ascends hi hi
  · simp [h_surface] at hi
  · generalize_proofs
    simp only [finIco, Fin.val_zero, Fin.val_last, List.length_append, List.length_map,
      List.length_pmap, List.Ico.length, tsub_zero, (x.pairable.snd _).def]
    apply Nat.add_sub_of_le
    apply Nat.le_of_lt_succ
    assumption
  · generalize_proofs
    simp only [finIco, Fin.val_zero, cutChild_val, h_surface, ↓reduceIte,
      (x.pairable.snd _).def, Pairable.transfer_last, Fin.val_last, List.append_assoc,
      List.length_append, List.length_map, List.length_pmap, List.Ico.length, tsub_zero,
      List.length_replicate]
    nth_rw 2 [← Nat.sub_one_add_one_eq_of_pos (List.length_pos_of_ne_nil (x.parents.index_get_ne_nil _))]
    rw [
      Nat.sub_add_comm (Pairable.transfer_last .. ▸ Nat.le_sub_one_of_lt (by assumption)),
      ← Nat.add_assoc _ _ 1, ← Nat.mul_succ, Nat.succ_eq_add_one, PNat.natPred_add_one,
      Nat.add_comm _ 1, ← Nat.add_assoc, Nat.add_right_cancel_iff, h_isbr]
    have :=
      congr_eqRec
        Option.get
        (badroot_of_last_surface_ne_one (by assumption) (by assumption) (by assumption))
        (by assumption)
    rw [← this, Option.get_map, Index₂.mk_val_snd, Index.last_val, (x.pairable.snd _).def]
    exact
      Nat.sub_add_cancel <| Nat.succ_le_of_lt <|
      List.length_pos_of_ne_nil <| x.parents.index_get_ne_nil _
  · simp [h_isbr, h_surface, ascends_badroot] at hi
  · generalize_proofs
    simp only [finIco, Fin.val_zero, (x.pairable.snd _).def, cutChild_val, hi.left,
      ↓reduceIte, Pairable.transfer_last, Fin.val_last, List.append_assoc, List.length_append,
      List.length_map, List.length_pmap, List.Ico.length, tsub_zero, List.length_replicate]
    rw [Nat.add_comm (_ * _), ← Nat.add_assoc,
      ← Nat.add_sub_assoc (Nat.le_of_lt_succ (by nth_rw 1 [← (x.pairable.snd _).def]; assumption)),
      Nat.add_sub_cancel_left]
  · generalize_proofs
    simp only [h_ascends, and_true, Decidable.not_not] at hi
    simp only [finIco, Fin.val_zero, (x.pairable.snd _).def, cutChild_val, hi, ↓reduceIte,
      Pairable.transfer_last, Fin.val_last, List.append_assoc, List.length_append, List.length_map,
      List.length_pmap, List.Ico.length, tsub_zero, List.length_replicate]
    have :=
      congr_eqRec
        Option.get
        (badroot_of_last_height_ne_one_of_last_surface_eq_one
          (by assumption)
          (by assumption)
          h.last_length_ne_one
          (by assumption))
        (by assumption)
    simp [← this]
  · simp [h_ascends] at hi
  · simp [finIco, (x.pairable.snd _).def]

theorem copySeam_ne_nil {x : Mountain} (h : x.IsLimit) (i : Index x.values.val) (k : ℕ+) :
    copySeam h i k ≠ [] :=
  by
  rw [← List.length_pos_iff_ne_nil, copySeam_length]
  split_ifs
  · exact Nat.add_pos_left (List.length_pos_of_ne_nil (x.values.index_get_ne_nil _)) _
  · exact List.length_pos_of_ne_nil (x.values.index_get_ne_nil _)

def shell {x : Mountain} (h : x.IsLimit) (n : ℕ) : ParentMountain :=
  ⟨x.parents.val.take (x.values.val.length - 1) ++
      ((List.Ico 1 (n + 1)).pmap Subtype.mk (fun _ h => (List.Ico.mem.mp h).left) |>.map
        fun k =>
          finIco
              ⟨((badroot ..).get h.badroot_isSome).val.fst,
                Nat.lt_add_right 1 (Index₂.val_fst_lt _)⟩
              ⟨x.values.val.length - 1, Nat.sub_lt_succ ..⟩ |>.map
            fun i => copySeam h i k).flatten,
    by
    intro l hl
    rw [List.mem_append] at hl
    cases hl with
    | inl hl =>
      obtain ⟨i, rfl⟩ := Index.get_of_mem (List.mem_of_mem_take hl)
      exact x.parents.index_get_ne_nil _
    | inr hl =>
      simp only [List.mem_flatten, List.mem_map, List.mem_pmap, List.Ico.mem,
        exists_exists_and_eq_and] at hl
      obtain ⟨k, ⟨_, ⟨_, _, rfl⟩⟩⟩ := hl
      exact copySeam_ne_nil _ _ _⟩

end Copy

end Ysequence
