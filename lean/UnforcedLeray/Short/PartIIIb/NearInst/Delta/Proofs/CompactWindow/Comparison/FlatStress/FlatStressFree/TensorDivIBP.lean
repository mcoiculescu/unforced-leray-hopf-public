import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_delta_8_2_3_4
import UnforcedLeray.Lib.Cylinder.IBP

/-!
# `tensorDivIBP` (item `PartIII-b:C/near/delta/8/2/3/4/org/2`)

Integration by parts of the planar tensor divergence against a flat test (source
`the November 2 reference manuscript` 1660-1665, 3420-3424).

The integrand `Σ_i (div₀M)_i Φ_i + Σ_{ij} M_ij ∂_jΦ_i` is, slice by slice in `s`, the sum of the
`q`- and `η`-divergences of the fields `M_ij Φ_i` (product rule; `ε = 0`, so `opQ 0 = ∂_q`).
Each cell integral of a `q`-derivative of a periodic function and of an `η`-derivative of a
compactly supported function vanishes (`Cyl.integral_cell_deriv_q_of_periodic`,
`Cyl.integral_cell_deriv_eta`); Fubini (`setIntegral_prod`) gives the space-time statement.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory UnforcedLeray.Axi Set Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.PartIIIb.NearInst.Delta

open UnforcedLeray.Short.PartIIIb UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Short.PartIIIb.NearInst UnforcedLeray.Short.PartIIa
open UnforcedLeray.B0220 (Profile HSpace measureH)
open UnforcedLeray.B0223 (MeridC)
open UnforcedLeray.Short.IIIa (IsFlatTest flatGrad)

namespace TDI

/-! ## Elementary identities -/

theorem tvBlk00 (v : TensorVal) : tvBlk v 0 0 = v 0 := rfl
theorem tvBlk01 (v : TensorVal) : tvBlk v 0 1 = v 1 := rfl
theorem tvBlk10 (v : TensorVal) : tvBlk v 1 0 = v 1 := rfl
theorem tvBlk11 (v : TensorVal) : tvBlk v 1 1 = v 2 := rfl

theorem divEps_zero_0 (M : Profile → TensorVal) (p : Profile) :
    divEps 0 M p 0 = pdQ (fun q => M q 0) p + pdEta (fun q => M q 1) p := by
  simp [divEps, opQ]

theorem divEps_zero_1 (M : Profile → TensorVal) (p : Profile) :
    divEps 0 M p 1 = pdQ (fun q => M q 1) p + pdEta (fun q => M q 2) p := by
  simp [divEps, opQ]

/-! ## Slices of profile derivatives -/

theorem partialQ_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Profile → E} (hf : Differentiable ℝ f) (s : ℝ) (x : ℝ × ℝ) :
    UnforcedLeray.Cyl.partialQ (fun y => f (s, y)) x = pdQ f (s, x) := by
  have hl : HasDerivAt (fun q' : ℝ => ((s, (q', x.2)) : Profile)) ((0 : ℝ), ((1 : ℝ), (0 : ℝ)))
      x.1 :=
    (hasDerivAt_const x.1 s).prodMk ((hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2))
  exact ((hf (s, x)).hasFDerivAt.comp_hasDerivAt x.1 hl).deriv

theorem partialEta_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Profile → E} (hf : Differentiable ℝ f) (s : ℝ) (x : ℝ × ℝ) :
    UnforcedLeray.Cyl.partialEta (fun y => f (s, y)) x = pdEta f (s, x) := by
  have hl : HasDerivAt (fun η' : ℝ => ((s, (x.1, η')) : Profile)) ((0 : ℝ), ((0 : ℝ), (1 : ℝ)))
      x.2 :=
    (hasDerivAt_const x.2 s).prodMk ((hasDerivAt_const x.2 x.1).prodMk (hasDerivAt_id x.2))
  exact ((hf (s, x)).hasFDerivAt.comp_hasDerivAt x.2 hl).deriv

theorem diff_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Profile → E}
    (hf : Differentiable ℝ f) (s : ℝ) : Differentiable ℝ (fun y : ℝ × ℝ => f (s, y)) :=
  hf.comp ((differentiable_const s).prodMk differentiable_id)

theorem contDiff_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Profile → E}
    (hf : ContDiff ℝ ∞ f) (s : ℝ) : ContDiff ℝ ∞ (fun y : ℝ × ℝ => f (s, y)) :=
  hf.comp ((contDiff_const).prodMk contDiff_id)

theorem contDiff_coord (M : Profile → TensorVal) (hM : ContDiff ℝ ∞ M) (k : Fin 4) :
    ContDiff ℝ ∞ (fun p : Profile => M p k) :=
  ((EuclideanSpace.proj k : TensorVal →L[ℂ] ℂ).restrictScalars ℝ).contDiff.comp hM

theorem contDiff_tv (M : Profile → TensorVal) (hM : ContDiff ℝ ∞ M) (i j : Fin 2) :
    ContDiff ℝ ∞ (fun p : Profile => tvBlk (M p) i j) := by
  fin_cases i <;> fin_cases j
  · exact contDiff_coord M hM 0
  · exact contDiff_coord M hM 1
  · exact contDiff_coord M hM 1
  · exact contDiff_coord M hM 2

/-! ## Real and complex slices of the flat test -/

theorem partialQ_ofReal {φ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) (x : ℝ × ℝ) :
    UnforcedLeray.Cyl.partialQ (fun y => ((φ y : ℝ) : ℂ)) x =
      ((UnforcedLeray.Cyl.partialQ φ x : ℝ) : ℂ) :=
  (UnforcedLeray.Cyl.hasDerivAt_sliceQ hφ x.1 x.2).ofReal_comp.deriv

theorem partialEta_ofReal {φ : ℝ × ℝ → ℝ} (hφ : Differentiable ℝ φ) (x : ℝ × ℝ) :
    UnforcedLeray.Cyl.partialEta (fun y => ((φ y : ℝ) : ℂ)) x =
      ((UnforcedLeray.Cyl.partialEta φ x : ℝ) : ℂ) :=
  (UnforcedLeray.Cyl.hasDerivAt_sliceEta hφ x.1 x.2).ofReal_comp.deriv

theorem flatGrad_zero_eq {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} {s : ℝ} (x : ℝ × ℝ) {i : Fin 2}
    (hφ : Differentiable ℝ (fun y : ℝ × ℝ => Φ s y i)) :
    ((flatGrad Φ s x i 0 : ℝ) : ℂ) =
      UnforcedLeray.Cyl.partialQ (fun y => ((Φ s y i : ℝ) : ℂ)) x := by
  rw [partialQ_ofReal hφ]
  congr 1
  unfold flatGrad UnforcedLeray.B0579.pd
  rw [UnforcedLeray.Cyl.partialQ_eq_fderiv hφ x]
  rfl

theorem flatGrad_one_eq {Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ} {s : ℝ} (x : ℝ × ℝ) {i : Fin 2}
    (hφ : Differentiable ℝ (fun y : ℝ × ℝ => Φ s y i)) :
    ((flatGrad Φ s x i 1 : ℝ) : ℂ) =
      UnforcedLeray.Cyl.partialEta (fun y => ((Φ s y i : ℝ) : ℂ)) x := by
  rw [partialEta_ofReal hφ]
  congr 1
  unfold flatGrad UnforcedLeray.B0579.pd
  rw [UnforcedLeray.Cyl.partialEta_eq_fderiv hφ x]
  rfl

/-! ## Product rule on slices -/

theorem partialQ_mul {a b : ℝ × ℝ → ℂ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (z : ℝ × ℝ) :
    UnforcedLeray.Cyl.partialQ (fun w => a w * b w) z =
      a z * UnforcedLeray.Cyl.partialQ b z + UnforcedLeray.Cyl.partialQ a z * b z := by
  have h := ((UnforcedLeray.Cyl.hasDerivAt_sliceQ ha z.1 z.2).mul
    (UnforcedLeray.Cyl.hasDerivAt_sliceQ hb z.1 z.2)).deriv
  rw [add_comm]
  exact h

theorem partialEta_mul {a b : ℝ × ℝ → ℂ} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (z : ℝ × ℝ) :
    UnforcedLeray.Cyl.partialEta (fun w => a w * b w) z =
      a z * UnforcedLeray.Cyl.partialEta b z + UnforcedLeray.Cyl.partialEta a z * b z := by
  have h := ((UnforcedLeray.Cyl.hasDerivAt_sliceEta ha z.1 z.2).mul
    (UnforcedLeray.Cyl.hasDerivAt_sliceEta hb z.1 z.2)).deriv
  rw [add_comm]
  exact h

/-! ## The pointwise divergence identity -/

/-- The integrand of `tensorDivIBP`. -/
def gInt (M : Profile → TensorVal) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (p : Profile) : ℂ :=
  ∑ i : Fin 2, (divEps 0 M p i * (Φ p.1 p.2 i : ℂ) +
    ∑ j : Fin 2, tvBlk (M p) i j * (flatGrad Φ p.1 p.2 i j : ℂ))

theorem pointwise (M : Profile → TensorVal) (hM : Differentiable ℝ M)
    (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ)
    (hΦ : ∀ i, Differentiable ℝ (fun p : Profile => Φ p.1 p.2 i)) (s : ℝ) (x : ℝ × ℝ) :
    gInt M Φ (s, x) =
      ∑ i : Fin 2, (UnforcedLeray.Cyl.partialQ (fun y => tvBlk (M (s, y)) i 0 * (Φ s y i : ℂ)) x +
        UnforcedLeray.Cyl.partialEta (fun y => tvBlk (M (s, y)) i 1 * (Φ s y i : ℂ)) x) := by
  have hMk : ∀ k : Fin 4, Differentiable ℝ (fun p : Profile => M p k) := fun k =>
    ((EuclideanSpace.proj k : TensorVal →L[ℂ] ℂ).restrictScalars ℝ).differentiable.comp hM
  have hMs : ∀ k : Fin 4, Differentiable ℝ (fun y : ℝ × ℝ => M (s, y) k) := fun k =>
    diff_slice (hMk k) s
  have hΦc : ∀ i, Differentiable ℝ (fun y : ℝ × ℝ => ((Φ s y i : ℝ) : ℂ)) := fun i =>
    Complex.ofRealCLM.differentiable.comp (diff_slice (hΦ i) s)
  have hΦr : ∀ i, Differentiable ℝ (fun y : ℝ × ℝ => Φ s y i) := fun i => diff_slice (hΦ i) s
  have dQ0 : UnforcedLeray.Cyl.partialQ (fun y => M (s, y) 0) x = pdQ (fun q => M q 0) (s, x) :=
    partialQ_slice (hMk 0) s x
  have dQ1 : UnforcedLeray.Cyl.partialQ (fun y => M (s, y) 1) x = pdQ (fun q => M q 1) (s, x) :=
    partialQ_slice (hMk 1) s x
  have dE1 : UnforcedLeray.Cyl.partialEta (fun y => M (s, y) 1) x =
      pdEta (fun q => M q 1) (s, x) := partialEta_slice (hMk 1) s x
  have dE2 : UnforcedLeray.Cyl.partialEta (fun y => M (s, y) 2) x =
      pdEta (fun q => M q 2) (s, x) := partialEta_slice (hMk 2) s x
  unfold gInt
  simp only [Fin.sum_univ_two, tvBlk00, tvBlk01, tvBlk10, tvBlk11, divEps_zero_0, divEps_zero_1]
  rw [partialQ_mul (hMs 0) (hΦc 0) x, partialEta_mul (hMs 1) (hΦc 0) x,
    partialQ_mul (hMs 1) (hΦc 1) x, partialEta_mul (hMs 2) (hΦc 1) x]
  rw [← flatGrad_zero_eq x (hΦr 0), ← flatGrad_one_eq x (hΦr 0),
    ← flatGrad_zero_eq x (hΦr 1), ← flatGrad_one_eq x (hΦr 1)]
  rw [dQ0, dQ1, dE1, dE2]
  ring

/-! ## Continuity and vanishing -/

theorem flatGrad_zero_of_s (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (s : ℝ) (x : ℝ × ℝ) (i j : Fin 2)
    (h : ∀ y : ℝ × ℝ, Φ s y i = 0) : flatGrad Φ s x i j = 0 := by
  unfold flatGrad UnforcedLeray.B0579.pd
  have hf : (fun y : ℝ × ℝ => Φ s y i) = fun _ => 0 := funext h
  rw [hf]
  simp

theorem flatGrad_zero_of_far (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) {R : ℝ} (s : ℝ) (x : ℝ × ℝ)
    (i j : Fin 2) (hfar : ∀ y : ℝ × ℝ, R < |y.2| → Φ s y i = 0) (hx : R < |x.2|) :
    flatGrad Φ s x i j = 0 := by
  have hev : (fun y : ℝ × ℝ => Φ s y i) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_abs.comp continuous_snd)).mem_nhds hx]
      with y hy
    exact hfar y hy
  unfold flatGrad UnforcedLeray.B0579.pd
  rw [hev.fderiv_eq]
  simp

theorem gInt_zero_outside (M : Profile → TensorVal) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (s1 s2 R : ℝ)
    (hsupp : ∀ s x i, (s < s1 ∨ s2 < s ∨ R < |x.2|) → Φ s x i = 0) (p : Profile)
    (hp : p.1 < s1 ∨ s2 < p.1 ∨ R < |p.2.2|) : gInt M Φ p = 0 := by
  have hΦ0 : ∀ i, (Φ p.1 p.2 i : ℂ) = 0 := fun i => by
    rw [hsupp p.1 p.2 i hp]; simp
  have hfg : ∀ i j, (flatGrad Φ p.1 p.2 i j : ℂ) = 0 := by
    intro i j
    rcases hp with h | h | h
    · rw [flatGrad_zero_of_s Φ p.1 p.2 i j (fun y => hsupp p.1 y i (Or.inl h))]; simp
    · rw [flatGrad_zero_of_s Φ p.1 p.2 i j (fun y => hsupp p.1 y i (Or.inr (Or.inl h)))]; simp
    · rw [flatGrad_zero_of_far Φ p.1 p.2 i j (fun y hy => hsupp p.1 y i (Or.inr (Or.inr hy))) h]
      simp
  unfold gInt
  simp [hΦ0, hfg]

/-- The `(i,j)` entry of the integrand, as a function of the profile. -/
def HH (M : Profile → TensorVal) (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (i j : Fin 2) (p : Profile) : ℂ :=
  tvBlk (M p) i j * (Φ p.1 p.2 i : ℂ)

theorem HH_contDiff (M : Profile → TensorVal) (hM : ContDiff ℝ ∞ M)
    (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (hΦ : ∀ i, ContDiff ℝ ∞ (fun p : Profile => Φ p.1 p.2 i))
    (i j : Fin 2) : ContDiff ℝ ∞ (HH M Φ i j) :=
  (contDiff_tv M hM i j).mul (Complex.ofRealCLM.contDiff.comp (hΦ i))

theorem gInt_eq_pd (M : Profile → TensorVal) (hM : Differentiable ℝ M)
    (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (hΦ : ∀ i, Differentiable ℝ (fun p : Profile => Φ p.1 p.2 i))
    (hHd : ∀ i j, Differentiable ℝ (HH M Φ i j)) (p : Profile) :
    gInt M Φ p = ∑ i : Fin 2, (pdQ (HH M Φ i 0) p + pdEta (HH M Φ i 1) p) := by
  refine (pointwise M hM Φ hΦ p.1 p.2).trans ?_
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : UnforcedLeray.Cyl.partialQ (fun y => tvBlk (M (p.1, y)) i 0 * (Φ p.1 y i : ℂ)) p.2 =
      pdQ (HH M Φ i 0) p := partialQ_slice (hHd i 0) p.1 p.2
  have h2 : UnforcedLeray.Cyl.partialEta (fun y => tvBlk (M (p.1, y)) i 1 * (Φ p.1 y i : ℂ)) p.2 =
      pdEta (HH M Φ i 1) p := partialEta_slice (hHd i 1) p.1 p.2
  rw [h1, h2]

theorem gInt_continuous (M : Profile → TensorVal) (hM : ContDiff ℝ ∞ M)
    (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (hΦ : ∀ i, ContDiff ℝ ∞ (fun p : Profile => Φ p.1 p.2 i)) :
    Continuous (gInt M Φ) := by
  have hd : ∀ i j, Differentiable ℝ (HH M Φ i j) := fun i j =>
    (HH_contDiff M hM Φ hΦ i j).differentiable (by simp)
  have e : gInt M Φ = fun p => ∑ i : Fin 2, (pdQ (HH M Φ i 0) p + pdEta (HH M Φ i 1) p) :=
    funext (gInt_eq_pd M (hM.differentiable (by simp)) Φ
      (fun i => (hΦ i).differentiable (by simp)) hd)
  rw [e]
  refine continuous_finsetSum _ fun i _ => ?_
  refine Continuous.add ?_ ?_
  · unfold pdQ
    exact ((HH_contDiff M hM Φ hΦ i 0).continuous_fderiv (by simp)).clm_apply continuous_const
  · unfold pdEta
    exact ((HH_contDiff M hM Φ hΦ i 1).continuous_fderiv (by simp)).clm_apply continuous_const

/-! ## The slice identity and the space-time statement -/

theorem slice_integral (c : ℝ) (hc : 0 < c) (M : Profile → TensorVal) (hMT : IsTensorTest c M)
    (Φ : ℝ → ℝ × ℝ → Fin 2 → ℝ) (hΦ : IsFlatTest c Φ) (s : ℝ) :
    ∫ x in UnforcedLeray.B0579.cell c, gInt M Φ (s, x) = 0 := by
  obtain ⟨s1, s2, R, hs1, hsupp⟩ := hΦ.support
  have hMd : Differentiable ℝ M := hMT.smooth.differentiable (by simp)
  have hΦd : ∀ i, Differentiable ℝ (fun p : Profile => Φ p.1 p.2 i) :=
    fun i => (hΦ.smooth i).differentiable (by simp)
  have hcell : UnforcedLeray.Cyl.cell c = UnforcedLeray.B0579.cell c := by
    unfold UnforcedLeray.Cyl.cell UnforcedLeray.B0579.cell
    rw [neg_div]
  have hC : ∀ i j, ContDiff ℝ ∞ (fun y : ℝ × ℝ => tvBlk (M (s, y)) i j * (Φ s y i : ℂ)) :=
    fun i j => (contDiff_slice (contDiff_tv M hMT.smooth i j) s).mul
      (Complex.ofRealCLM.contDiff.comp (contDiff_slice (hΦ.smooth i) s))
  have hD : ∀ i j, Differentiable ℝ (fun y : ℝ × ℝ => tvBlk (M (s, y)) i j * (Φ s y i : ℂ)) :=
    fun i j => (hC i j).differentiable (by simp)
  have hVO : ∀ i j, UnforcedLeray.Cyl.VanishesOutside R
      (fun y : ℝ × ℝ => tvBlk (M (s, y)) i j * (Φ s y i : ℂ)) := fun i j =>
    UnforcedLeray.Cyl.VanishesOutside.mul_left
      (f := fun z : ℝ × ℝ => (Φ s z i : ℂ))
      (fun z hz => by simp [hsupp s z i (Or.inr (Or.inr hz))]) (fun y => tvBlk (M (s, y)) i j)
  have hper : ∀ i j, UnforcedLeray.Cyl.IsPeriodic c
      (fun y : ℝ × ℝ => tvBlk (M (s, y)) i j * (Φ s y i : ℂ)) := by
    intro i j z
    show tvBlk (M (s, (z.1 + c, z.2))) i j * (Φ s (z.1 + c, z.2) i : ℂ) =
      tvBlk (M (s, z)) i j * (Φ s z i : ℂ)
    rw [hMT.periodic (s, z), hΦ.periodic s z i]
  have hQint : ∀ i, IntegrableOn
      (UnforcedLeray.Cyl.partialQ (fun y : ℝ × ℝ => tvBlk (M (s, y)) i 0 * (Φ s y i : ℂ)))
      (UnforcedLeray.Cyl.cell c) := fun i =>
    (UnforcedLeray.Cyl.VanishesOutside.partialQ (hVO i 0)).integrableOn_cell
      (UnforcedLeray.Cyl.contDiff_partialQ (n := 0) ((hC i 0).of_le (by norm_num))).continuous c
  have hEint : ∀ i, IntegrableOn
      (UnforcedLeray.Cyl.partialEta (fun y : ℝ × ℝ => tvBlk (M (s, y)) i 1 * (Φ s y i : ℂ)))
      (UnforcedLeray.Cyl.cell c) := fun i =>
    (UnforcedLeray.Cyl.VanishesOutside.partialEta (hVO i 1)).integrableOn_cell
      (UnforcedLeray.Cyl.contDiff_partialEta (n := 0) ((hC i 1).of_le (by norm_num))).continuous c
  have hFint : ∀ i, IntegrableOn
      (fun y : ℝ × ℝ => tvBlk (M (s, y)) i 1 * (Φ s y i : ℂ)) (UnforcedLeray.Cyl.cell c) := fun i =>
    (hVO i 1).integrableOn_cell (hC i 1).continuous c
  have hA : ∀ i, IntegrableOn (fun x : ℝ × ℝ =>
      UnforcedLeray.Cyl.partialQ (fun y : ℝ × ℝ => tvBlk (M (s, y)) i 0 * (Φ s y i : ℂ)) x +
        UnforcedLeray.Cyl.partialEta (fun y : ℝ × ℝ => tvBlk (M (s, y)) i 1 * (Φ s y i : ℂ)) x)
      (UnforcedLeray.Cyl.cell c) := fun i => (hQint i).add (hEint i)
  have hQ0 : ∀ i, ∫ y in UnforcedLeray.Cyl.cell c,
      UnforcedLeray.Cyl.partialQ (fun y : ℝ × ℝ => tvBlk (M (s, y)) i 0 * (Φ s y i : ℂ)) y = 0 :=
    fun i => UnforcedLeray.Cyl.integral_cell_deriv_q_of_periodic hc (hper i 0)
      (fun q η => UnforcedLeray.Cyl.hasDerivAt_sliceQ (hD i 0) q η) (hQint i)
  have hE0 : ∀ i, ∫ y in UnforcedLeray.Cyl.cell c,
      UnforcedLeray.Cyl.partialEta (fun y : ℝ × ℝ => tvBlk (M (s, y)) i 1 * (Φ s y i : ℂ)) y = 0 :=
    fun i => UnforcedLeray.Cyl.integral_cell_deriv_eta
      (fun q η => UnforcedLeray.Cyl.hasDerivAt_sliceEta (hD i 1) q η) (hFint i) (hEint i)
  rw [← hcell]
  have hfun : (fun x : ℝ × ℝ => gInt M Φ (s, x)) = fun x : ℝ × ℝ =>
      ∑ i : Fin 2, (UnforcedLeray.Cyl.partialQ
          (fun y : ℝ × ℝ => tvBlk (M (s, y)) i 0 * (Φ s y i : ℂ)) x +
        UnforcedLeray.Cyl.partialEta
          (fun y : ℝ × ℝ => tvBlk (M (s, y)) i 1 * (Φ s y i : ℂ)) x) :=
    funext fun x => pointwise M hMd Φ hΦd s x
  rw [hfun]
  simp only [Fin.sum_univ_two]
  rw [integral_add (hA 0) (hA 1), integral_add (hQint 0) (hEint 0),
    integral_add (hQint 1) (hEint 1), hQ0 0, hE0 0, hQ0 1, hE0 1]
  simp

end TDI

open TDI in
/-- **`tensorDivIBP`** (source 1660-1665, 3420-3424): the integration by parts of the tensor
divergence against a flat test. -/
theorem tensorDivIBP : TensorDivIBP := by
  intro c hc M hMT Φ hΦ
  obtain ⟨s1, s2, R, hs1, hsupp⟩ := hΦ.support
  have hK : IsCompact (Icc s1 s2 ×ˢ (Icc (-(c / 2)) (c / 2) ×ˢ Icc (-R) R)) :=
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
  have hI : IntegrableOn (gInt M Φ) (Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c) := by
    refine ((gInt_continuous M hMT.smooth Φ hΦ.smooth).continuousOn.integrableOn_compact hK
      ).of_forall_sdiff_eq_zero
      (measurableSet_Ioi.prod (UnforcedLeray.B0579.measurableSet_cell c)) ?_
    intro p hp
    apply gInt_zero_outside M Φ s1 s2 R hsupp p
    by_contra hcon
    push_neg at hcon
    obtain ⟨h1, h2, h3⟩ := hcon
    apply hp.2
    have hq : p.2 ∈ UnforcedLeray.B0579.cell c := hp.1.2
    exact ⟨⟨h1, h2⟩, ⟨⟨hq.1.1, hq.1.2.le⟩, abs_le.1 h3⟩⟩
  refine ⟨hI, ?_⟩
  have hS : ∀ s : ℝ, ∫ x in UnforcedLeray.B0579.cell c, gInt M Φ (s, x) = 0 :=
    fun s => slice_integral c hc M hMT Φ hΦ s
  show (∫ p in Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c, gInt M Φ p) = 0
  rw [show (∫ p in Ioi (0 : ℝ) ×ˢ UnforcedLeray.B0579.cell c, gInt M Φ p) =
      ∫ x in Ioi (0 : ℝ), ∫ y in UnforcedLeray.B0579.cell c, gInt M Φ (x, y) from
    setIntegral_prod (gInt M Φ) hI]
  simp only [hS, integral_zero]

end UnforcedLeray.Short.PartIIIb.NearInst.Delta
