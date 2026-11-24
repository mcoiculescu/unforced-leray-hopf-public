import UnforcedLeray.Lib.Sobolev.Space
import UnforcedLeray.Analysis.SobolevGraph.H2

/-!
# Isometric bridges to the compiled `SobolevGraph.H1` and `SobolevGraph.H2` (INF11 target S3)

Scoping note `INF11-INF14-Sobolev.md` §5.1 (S3) and bypass B8 ("The compiled `H1`/`H2` are
kept and bridged by isometries, so no compiled consumer is refactored"); decision D3 of the
scoping README ("`SobolevGraph.H1/H2` are reached through the isometries of INF11 S3").

The compiled spaces (`lean/UnforcedLeray/Analysis/SobolevGraph/H1.lean:60`, `H2.lean:81`)
are the closed graphs of the target statement's `HasWeakSpatialDerivative`
(`Statement.lean:65`) in `L²(ℝ³; ℝ³)`. They are the instances `k = 1, 2`, `p = 2`, `ρ = 1`,
`D = wholeSpace 3`, `𝕜 = ℝ`, `F = Space` of `Sob.W`; the bridges below are linear isometric
equivalences that are the identity on every component, almost everywhere (`h1Equiv_value`,
`h1Equiv_deriv`, `h2Equiv_value`, `h2Equiv_deriv₁`, `h2Equiv_deriv₂`). The second derivative `second i j`
of `H2` (`j`-th derivative of the `i`-th first derivative) is the word `[e i, e j]`.

## Main declarations
* `Submodule.isometryEquivOfMemIff`: an ambient isometry restricted to matching submodules;
* `lpToW : L²(ℝ³; ℝ³) ≃ₗᵢ L²(1 · dμ)` for `μ = (wholeSpace 3).μ` (the identity on functions,
  `coeFn_lpToW`); the transport goes through `MemLp.toLp`, so no two `Lp` types are identified
  definitionally;
* `idx1Equiv : Fin 4 ≃ Idx 3 1`, `idx2Equiv : H2Index ≃ Idx 3 2`;
* `h1Equiv : SobolevGraph.H1 ≃ₗᵢ[ℝ] W (wholeSpace 3) 1 ℝ Space 1 2`, `h1Equiv_value`,
  `h1Equiv_deriv` (components agree a.e.);
* `h2Equiv : SobolevGraph.H2 ≃ₗᵢ[ℝ] W (wholeSpace 3) 1 ℝ Space 2 2`, `h2Equiv_value`,
  `h2Equiv_deriv₁`, `h2Equiv_deriv₂`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

namespace UnforcedLeray.Sob

/-- An isometric equivalence of ambient spaces carrying `P` onto `Q` restricts to an
isometric equivalence `P ≃ₗᵢ Q`. -/
def _root_.Submodule.isometryEquivOfMemIff {𝕜 M N : Type*} [RCLike 𝕜] [NormedAddCommGroup M]
    [NormedSpace 𝕜 M] [NormedAddCommGroup N] [NormedSpace 𝕜 N] (T : M ≃ₗᵢ[𝕜] N)
    (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N) (h : ∀ x, x ∈ P ↔ T x ∈ Q) : P ≃ₗᵢ[𝕜] Q where
  toFun x := ⟨T x, (h x).1 x.2⟩
  invFun y := ⟨T.symm y, (h _).2 (by simpa using y.2)⟩
  map_add' x y := Subtype.ext (map_add T _ _)
  map_smul' c x := Subtype.ext (map_smul T _ _)
  left_inv x := Subtype.ext (T.symm_apply_apply _)
  right_inv y := Subtype.ext (T.apply_symm_apply _)
  norm_map' x := T.norm_map (x : M)

@[simp] theorem _root_.Submodule.coe_isometryEquivOfMemIff {𝕜 M N : Type*} [RCLike 𝕜]
    [NormedAddCommGroup M] [NormedSpace 𝕜 M] [NormedAddCommGroup N] [NormedSpace 𝕜 N]
    (T : M ≃ₗᵢ[𝕜] N) (P : Submodule 𝕜 M) (Q : Submodule 𝕜 N) (h : ∀ x, x ∈ P ↔ T x ∈ Q)
    (x : P) : (Submodule.isometryEquivOfMemIff T P Q h x : N) = T x := rfl

/-! ### The index equivalences -/

/-- Two words with the same length and the same letters are equal. -/
theorem Idx.mk_eq_mk {n k : ℕ} {j : Fin (k + 1)} {β γ : Fin j → Fin n} (h : ∀ i, β i = γ i) :
    (⟨j, β⟩ : Idx n k) = ⟨j, γ⟩ := by
  rw [funext h]

/-- `Fin 4 ≃ Idx 3 1`: slot `0` is the field, slot `i.succ` the derivative `∂_i`. -/
def idx1Equiv : Fin 4 ≃ Idx 3 1 where
  toFun j := Fin.cases Idx.zero (fun i => Idx.cons i Idx.zero) j
  invFun α := if h : (α.1 : ℕ) = 0 then 0 else (α.2 ⟨0, by omega⟩).succ
  left_inv j := by
    refine Fin.cases ?_ (fun i => ?_) j
    · rfl
    · simp [Idx.cons]
  right_inv := by
    rintro ⟨⟨j, hj⟩, β⟩
    rcases j with _ | _ | j
    · exact Idx.mk_eq_mk fun i => i.elim0
    · refine Idx.mk_eq_mk fun i => ?_
      obtain ⟨_ | m, hm⟩ := i
      · rfl
      · exact absurd hm (by omega)
    · exact absurd hj (by omega)

@[simp] theorem idx1Equiv_zero : idx1Equiv 0 = Idx.zero := rfl

@[simp] theorem idx1Equiv_succ (i : Fin 3) : idx1Equiv i.succ = Idx.cons i Idx.zero := rfl

theorem idx1Equiv_symm_zero : idx1Equiv.symm Idx.zero = 0 := by
  rw [Equiv.symm_apply_eq, idx1Equiv_zero]

open SobolevGraph in
/-- `H2Index ≃ Idx 3 2`: the field, `∂_i`, and `second i j = ∂_j ∂_i ↦ [e i, e j]`. -/
def idx2Equiv : H2Index ≃ Idx 3 2 where
  toFun
    | Sum.inl _ => Idx.zero
    | Sum.inr (Sum.inl i) => Idx.cons i Idx.zero
    | Sum.inr (Sum.inr (i, j)) => Idx.cons i (Idx.cons j Idx.zero)
  invFun α :=
    if h0 : (α.1 : ℕ) = 0 then Sum.inl ()
    else if h1 : (α.1 : ℕ) = 1 then Sum.inr (Sum.inl (α.2 ⟨0, by omega⟩))
    else Sum.inr (Sum.inr (α.2 ⟨0, by omega⟩, α.2 ⟨1, by omega⟩))
  left_inv := by
    rintro (⟨⟩ | i | ⟨i, j⟩) <;> rfl
  right_inv := by
    rintro ⟨⟨j, hj⟩, β⟩
    rcases j with _ | _ | _ | j
    · exact Idx.mk_eq_mk fun i => i.elim0
    · refine Idx.mk_eq_mk fun i => ?_
      obtain ⟨_ | m, hm⟩ := i
      · rfl
      · exact absurd hm (by simp [Idx.zero, Idx.cons])
    · refine Idx.mk_eq_mk fun i => ?_
      obtain ⟨_ | _ | m, hm⟩ := i
      · rfl
      · rfl
      · exact absurd hm (by simp [Idx.zero, Idx.cons])
    · exact absurd hj (by omega)

/-! ### `L²(ℝ³)` as the unweighted `L²` of `wholeSpace 3` -/

theorem integrable_smul_l2 {φ : Space → ℝ} (hφ : (wholeSpace 3).Adm φ) (f : L2Space) :
    Integrable (fun x => φ x • f x) volume := by
  have hf : MemLp (f : Space → Space) 2 (wμ (wholeSpace 3).μ 1) := by
    rw [wμ_one]; exact Lp.memLp f
  exact integrable_smul_of_memLp (CompactlyBounded.of_adm hφ) hf

/-- The unweighted measure of `wholeSpace 3` is Lebesgue measure on `Space`. -/
theorem wμ_wholeSpace_one : wμ (wholeSpace 3).μ 1 = (volume : Measure Space) := by
  rw [wμ_one]; rfl

theorem memLp_toW (f : L2Space) : MemLp (f : Space → Space) 2 (wμ (wholeSpace 3).μ 1) := by
  rw [wμ_wholeSpace_one]; exact Lp.memLp f

theorem memLp_ofW (g : Lp Space 2 (wμ (wholeSpace 3).μ (1 : Weight Space))) :
    MemLp (g : Space → Space) 2 (volume : Measure Space) :=
  (Lp.memLp g).mono_measure wμ_wholeSpace_one.symm.le

theorem ae_wμ_one_iff {P : Space → Prop} :
    (∀ᵐ x ∂(wμ (wholeSpace 3).μ 1), P x) ↔ ∀ᵐ x ∂(volume : Measure Space), P x := by
  rw [wμ_wholeSpace_one]

/-- `L²(ℝ³; ℝ³)` is the unweighted `L²` of `wholeSpace 3` (the identity on functions). -/
def lpToW : L2Space ≃ₗᵢ[ℝ] Lp Space 2 (wμ (wholeSpace 3).μ (1 : Weight Space)) where
  toFun f := (memLp_toW f).toLp _
  invFun g := (memLp_ofW g).toLp _
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(memLp_toW (f + g)).coeFn_toLp, (memLp_toW f).coeFn_toLp,
      (memLp_toW g).coeFn_toLp, Lp.coeFn_add ((memLp_toW f).toLp _) ((memLp_toW g).toLp _),
      ae_wμ_one_iff.mpr (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
    simp only [h1, h2, h3, h4, h5, Pi.add_apply]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(memLp_toW (c • f)).coeFn_toLp, (memLp_toW f).coeFn_toLp,
      Lp.coeFn_smul c ((memLp_toW f).toLp _), ae_wμ_one_iff.mpr (Lp.coeFn_smul c f)]
      with x h1 h2 h3 h4
    simp only [RingHom.id_apply, h1, h2, h3, h4, Pi.smul_apply]
  left_inv f := by
    apply Lp.ext
    filter_upwards [(memLp_ofW ((memLp_toW f).toLp _)).coeFn_toLp,
      ae_wμ_one_iff.mp (memLp_toW f).coeFn_toLp] with x h1 h2
    simp only [h1, h2]
  right_inv g := by
    apply Lp.ext
    filter_upwards [(memLp_toW ((memLp_ofW g).toLp _)).coeFn_toLp,
      ae_wμ_one_iff.mpr (memLp_ofW g).coeFn_toLp] with x h1 h2
    simp only [h1, h2]
  norm_map' f := by
    change ‖(memLp_toW f).toLp _‖ = ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    congr 1
    rw [wμ_wholeSpace_one] <;> rfl

theorem lpToW_apply (f : L2Space) : lpToW f = (memLp_toW f).toLp _ := rfl

/-- `lpToW` is the identity on functions, `(wholeSpace 3).μ`-almost everywhere. -/
theorem coeFn_lpToW (f : L2Space) :
    ⇑(lpToW f) =ᵐ[(wholeSpace 3).μ] (f : Space → Space) :=
  (ae_eq_wμ_iff (wholeSpace 3).μ 1).mp (memLp_toW f).coeFn_toLp

/-! ### `H¹` -/

/-- The ambient isometry `PiLp 2 (Fin 4 → L²) ≃ SobTuple (wholeSpace 3) 1 Space 1 2`. -/
def h1Ambient : SobolevGraph.H1Ambient ≃ₗᵢ[ℝ] SobTuple (wholeSpace 3) 1 Space 1 2 :=
  (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : Fin 4 => lpToW)).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ (Lp Space 2 (wμ (wholeSpace 3).μ (1 : Weight Space)))
      idx1Equiv)

theorem h1Ambient_apply (x : SobolevGraph.H1Ambient) (α : Idx 3 1) :
    (h1Ambient x).ofLp α = lpToW (x.ofLp (idx1Equiv.symm α)) := rfl

theorem coeFn_h1Ambient (x : SobolevGraph.H1Ambient) (α : Idx 3 1) :
    ⇑((h1Ambient x).ofLp α) =ᵐ[(wholeSpace 3).μ] ⇑(x.ofLp (idx1Equiv.symm α)) := by
  rw [h1Ambient_apply]; exact coeFn_lpToW _

theorem idx1Equiv_symm_cons (i : Fin 3) : idx1Equiv.symm (Idx.cons i Idx.zero) = i.succ := by
  rw [Equiv.symm_apply_eq, idx1Equiv_succ]

theorem mem_SobSub_h1Ambient_iff (x : SobolevGraph.H1Ambient) :
    x ∈ SobolevGraph.H1Sub ↔ h1Ambient x ∈ SobSub (wholeSpace 3) 1 ℝ Space 1 2 := by
  have h0 := coeFn_h1Ambient x Idx.zero
  rw [idx1Equiv_symm_zero] at h0
  rw [SobolevGraph.mem_H1Sub_iff, mem_SobSub_iff]
  constructor
  · intro h α
    have key : ∀ j : Fin 4, HasWeakDeriv (wholeSpace 3) ((wholeSpace 3).word (idx1Equiv j))
        (x.ofLp 0 : Space → Space) (x.ofLp j : Space → Space) := by
      intro j
      induction j using Fin.cases with
      | zero =>
        rw [idx1Equiv_zero, TestDomain.word_zero]
        exact HasWeakDeriv.nil fun φ hφ => integrable_smul_l2 hφ _
      | succ i =>
        rw [idx1Equiv_succ, TestDomain.word_cons, TestDomain.word_zero, wholeSpace_dir]
        exact hasWeakSpatialDerivative_iff.mp (h i)
    have hk := key (idx1Equiv.symm α)
    rw [Equiv.apply_symm_apply] at hk
    exact hk.congr_ae h0.symm (coeFn_h1Ambient x α).symm
  · intro h i
    have h1 := h (Idx.cons i Idx.zero)
    rw [TestDomain.word_cons, TestDomain.word_zero, wholeSpace_dir] at h1
    have hi := coeFn_h1Ambient x (Idx.cons i Idx.zero)
    rw [idx1Equiv_symm_cons] at hi
    exact hasWeakSpatialDerivative_iff.mpr (h1.congr_ae h0 hi)

/-- **`H¹` bridge** (S3): the compiled `SobolevGraph.H1` is isometrically `W^{1,2}(ℝ³; ℝ³)`. -/
def h1Equiv : SobolevGraph.H1 ≃ₗᵢ[ℝ] W (wholeSpace 3) 1 ℝ Space 1 2 :=
  Submodule.isometryEquivOfMemIff h1Ambient _ _ mem_SobSub_h1Ambient_iff

/-- The field of `h1Equiv u` is the field of `u` (a.e.). -/
theorem h1Equiv_value (u : SobolevGraph.H1) :
    ⇑(W.value (wholeSpace 3) 1 ℝ Space 1 2 (h1Equiv u)) =ᵐ[(wholeSpace 3).μ] ⇑u.value := by
  have h := coeFn_h1Ambient (u : SobolevGraph.H1Ambient) Idx.zero
  rw [idx1Equiv_symm_zero] at h
  exact h

/-- The derivative `∂ᵢ` of `h1Equiv u` is the `i`-th derivative of `u` (a.e.). -/
theorem h1Equiv_deriv (u : SobolevGraph.H1) (i : Fin 3) :
    ⇑(W.deriv (wholeSpace 3) 1 ℝ Space 1 2 (Idx.cons i Idx.zero) (h1Equiv u)) =ᵐ[(wholeSpace 3).μ]
      ⇑(u.derivative i) := by
  have h := coeFn_h1Ambient (u : SobolevGraph.H1Ambient) (Idx.cons i Idx.zero)
  rw [idx1Equiv_symm_cons] at h
  exact h

/-! ### `H²` -/

@[simp] theorem idx2Equiv_inl (u : Unit) : idx2Equiv (Sum.inl u) = Idx.zero := rfl

@[simp] theorem idx2Equiv_first (i : Fin 3) :
    idx2Equiv (Sum.inr (Sum.inl i)) = Idx.cons i Idx.zero := rfl

@[simp] theorem idx2Equiv_second (i j : Fin 3) :
    idx2Equiv (Sum.inr (Sum.inr (i, j))) = Idx.cons i (Idx.cons j Idx.zero) := rfl

theorem idx2Equiv_symm_zero : idx2Equiv.symm Idx.zero = SobolevGraph.h2ValueIndex := by
  rw [Equiv.symm_apply_eq]; exact (idx2Equiv_inl ()).symm

theorem idx2Equiv_symm_first (i : Fin 3) :
    idx2Equiv.symm (Idx.cons i Idx.zero) = SobolevGraph.h2FirstIndex i := by
  rw [Equiv.symm_apply_eq]; exact (idx2Equiv_first i).symm

theorem idx2Equiv_symm_second (i j : Fin 3) :
    idx2Equiv.symm (Idx.cons i (Idx.cons j Idx.zero)) = SobolevGraph.h2SecondIndex i j := by
  rw [Equiv.symm_apply_eq]; exact (idx2Equiv_second i j).symm

/-- The ambient isometry `PiLp 2 (H2Index → L²) ≃ SobTuple (wholeSpace 3) 1 Space 2 2`. -/
def h2Ambient : SobolevGraph.H2Ambient ≃ₗᵢ[ℝ] SobTuple (wholeSpace 3) 1 Space 2 2 :=
  (LinearIsometryEquiv.piLpCongrRight 2 (fun _ : SobolevGraph.H2Index => lpToW)).trans
    (LinearIsometryEquiv.piLpCongrLeft 2 ℝ (Lp Space 2 (wμ (wholeSpace 3).μ (1 : Weight Space)))
      idx2Equiv)

theorem h2Ambient_apply (x : SobolevGraph.H2Ambient) (α : Idx 3 2) :
    (h2Ambient x).ofLp α = lpToW (x.ofLp (idx2Equiv.symm α)) := rfl

theorem coeFn_h2Ambient (x : SobolevGraph.H2Ambient) (α : Idx 3 2) :
    ⇑((h2Ambient x).ofLp α) =ᵐ[(wholeSpace 3).μ] ⇑(x.ofLp (idx2Equiv.symm α)) := by
  rw [h2Ambient_apply]; exact coeFn_lpToW _

theorem mem_SobSub_h2Ambient_iff (x : SobolevGraph.H2Ambient) :
    x ∈ SobolevGraph.H2Sub ↔ h2Ambient x ∈ SobSub (wholeSpace 3) 1 ℝ Space 2 2 := by
  have h0 := coeFn_h2Ambient x Idx.zero
  rw [idx2Equiv_symm_zero] at h0
  have h1f : ∀ i : Fin 3, ⇑((h2Ambient x).ofLp (Idx.cons i Idx.zero)) =ᵐ[(wholeSpace 3).μ]
      ⇑(x.ofLp (SobolevGraph.h2FirstIndex i)) := fun i => by
    have := coeFn_h2Ambient x (Idx.cons i Idx.zero)
    rwa [idx2Equiv_symm_first] at this
  have h2f : ∀ i j : Fin 3, ⇑((h2Ambient x).ofLp (Idx.cons i (Idx.cons j Idx.zero)))
      =ᵐ[(wholeSpace 3).μ] ⇑(x.ofLp (SobolevGraph.h2SecondIndex i j)) := fun i j => by
    have := coeFn_h2Ambient x (Idx.cons i (Idx.cons j Idx.zero))
    rwa [idx2Equiv_symm_second] at this
  rw [SobolevGraph.mem_H2Sub_iff, mem_SobSub_iff]
  constructor
  · rintro ⟨hA, hB⟩
    have key : ∀ j : SobolevGraph.H2Index, HasWeakDeriv (wholeSpace 3)
        ((wholeSpace 3).word (idx2Equiv j)) (x.ofLp SobolevGraph.h2ValueIndex : Space → Space)
        (x.ofLp j : Space → Space) := by
      rintro (⟨⟩ | i | ⟨i, j⟩)
      · rw [idx2Equiv_inl, TestDomain.word_zero]
        exact HasWeakDeriv.nil fun φ hφ => integrable_smul_l2 hφ _
      · rw [idx2Equiv_first, TestDomain.word_cons, TestDomain.word_zero, wholeSpace_dir]
        exact hasWeakSpatialDerivative_iff.mp (hA i)
      · rw [idx2Equiv_second, TestDomain.word_cons, TestDomain.word_cons, TestDomain.word_zero,
          wholeSpace_dir]
        exact (hasWeakSpatialDerivative_iff.mp (hA i)).append
          (hasWeakSpatialDerivative_iff.mp (hB i j))
    intro α
    have hk := key (idx2Equiv.symm α)
    rw [Equiv.apply_symm_apply] at hk
    exact hk.congr_ae h0.symm (coeFn_h2Ambient x α).symm
  · intro h
    have hA : ∀ i : Fin 3, HasWeakDeriv (wholeSpace 3) [e i]
        (x.ofLp SobolevGraph.h2ValueIndex : Space → Space)
        (x.ofLp (SobolevGraph.h2FirstIndex i) : Space → Space) := fun i => by
      have := h (Idx.cons i Idx.zero)
      rw [TestDomain.word_cons, TestDomain.word_zero, wholeSpace_dir] at this
      exact this.congr_ae h0 (h1f i)
    refine ⟨fun i => hasWeakSpatialDerivative_iff.mpr (hA i), fun i j =>
      hasWeakSpatialDerivative_iff.mpr ?_⟩
    have := h (Idx.cons i (Idx.cons j Idx.zero))
    rw [TestDomain.word_cons, TestDomain.word_cons, TestDomain.word_zero, wholeSpace_dir] at this
    exact (hA i).of_cons (this.congr_ae h0 (h2f i j))

/-- **`H²` bridge** (S3): the compiled `SobolevGraph.H2` is isometrically `W^{2,2}(ℝ³; ℝ³)`,
with `second i j ↦ [e i, e j]`. -/
def h2Equiv : SobolevGraph.H2 ≃ₗᵢ[ℝ] W (wholeSpace 3) 1 ℝ Space 2 2 :=
  Submodule.isometryEquivOfMemIff h2Ambient _ _ mem_SobSub_h2Ambient_iff

theorem h2Equiv_value (u : SobolevGraph.H2) :
    ⇑(W.value (wholeSpace 3) 1 ℝ Space 2 2 (h2Equiv u)) =ᵐ[(wholeSpace 3).μ] ⇑u.value := by
  have h := coeFn_h2Ambient (u : SobolevGraph.H2Ambient) Idx.zero
  rw [idx2Equiv_symm_zero] at h
  exact h

theorem h2Equiv_deriv₁ (u : SobolevGraph.H2) (i : Fin 3) :
    ⇑(W.deriv (wholeSpace 3) 1 ℝ Space 2 2 (Idx.cons i Idx.zero) (h2Equiv u))
      =ᵐ[(wholeSpace 3).μ] ⇑(u.first i) := by
  have h := coeFn_h2Ambient (u : SobolevGraph.H2Ambient) (Idx.cons i Idx.zero)
  rw [idx2Equiv_symm_first] at h
  exact h

theorem h2Equiv_deriv₂ (u : SobolevGraph.H2) (i j : Fin 3) :
    ⇑(W.deriv (wholeSpace 3) 1 ℝ Space 2 2 (Idx.cons i (Idx.cons j Idx.zero)) (h2Equiv u))
      =ᵐ[(wholeSpace 3).μ] ⇑(u.second i j) := by
  have h := coeFn_h2Ambient (u : SobolevGraph.H2Ambient) (Idx.cons i (Idx.cons j Idx.zero))
  rw [idx2Equiv_symm_second] at h
  exact h

end UnforcedLeray.Sob
