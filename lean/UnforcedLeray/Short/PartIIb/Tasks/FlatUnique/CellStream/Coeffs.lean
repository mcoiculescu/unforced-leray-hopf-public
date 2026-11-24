import UnforcedLeray.Short.PartIIb.Sub.T11_1
import UnforcedLeray.Short.PartIIb.Tasks.FlatUnique.CellStream.HrBox

/-!
# Part II-b, leaf `PartII-b:T11/1/5` (`CellStreamCoeffs`): the coefficient profiles `G_0, …, G_3`

Source of record: `the November 2 reference manuscript` (the flat equation tested
against planar solenoidal tests, SP 1923-1927; the source line range 1915-1930 is the flat
estimate block that the cell-stream coefficients come from). Statement: `CellStreamCoeffs` of
`Sub/T11_1.lean`, unchanged; no hypotheses are added.

## Proof

Each profile is linear in `b` with continuous coefficients: `cellG ν μ b ψ k x = b x 0 * a0 x +
b x 1 * a1 x`, where `a0, a1` are built from `x.1`, `ψ` and its `cpd`-derivatives (for `k = 0`, from
`flatTranspose`, which involves derivatives of `ψ` up to order three).

* Periodicity. `ψ` is `c`-periodic in `q` everywhere, so every `cpd`-derivative of `ψ` is
  `c`-periodic everywhere (`coef_cpd_per`, from `fderiv_comp_add_right`). `x.1` is unchanged by
  `qShift`. `b` is `c`-periodic almost everywhere (`InHr.periodic`).
* Vanishing. `ψ = 0` on the open set `coefU = {x.1 < σ} ∪ {H < x.1} ∪ {L < |x.2.2|}`, hence every
  `cpd`-derivative of `ψ` vanishes on `coefU` (`coef_cpd_vanish`, via
  `Filter.EventuallyEq.fderiv_eq`).
* Integrability. `hrBoxIntegrable` gives `IntegrableOn (b · i)` on each box, the box is compact and
  the coefficients are continuous, so `IntegrableOn.mul_continuousOn` applies to each product.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

/-- The open region `{x.1 < σ} ∪ {H < x.1} ∪ {L < |x.2.2|}` outside of which the stream is
required to vanish (the hypothesis region of `CellStreamCoeffs`). -/
def coefU (σ H L : ℝ) : Set Coord := {x | x.1 < σ ∨ H < x.1 ∨ L < |x.2.2|}

theorem coef_qShift_fst (c : ℝ) (y : Coord) : (qShift c y).1 = y.1 := rfl

theorem coef_isOpen (σ H L : ℝ) : IsOpen (coefU σ H L) := by
  have h1 : IsOpen {x : Coord | x.1 < σ} := isOpen_lt continuous_fst continuous_const
  have h2 : IsOpen {x : Coord | H < x.1} := isOpen_lt continuous_const continuous_fst
  have h3 : IsOpen {x : Coord | L < |x.2.2|} :=
    isOpen_lt continuous_const (by fun_prop)
  unfold coefU
  simp only [Set.ofPred_or]
  exact h1.union (h2.union h3)

/-! ## `cpd` of smooth and of periodic functions -/

theorem coef_cpd_contDiff {φ : Coord → ℝ} (hφ : ContDiff ℝ ∞ φ) (j : Fin 3) :
    ContDiff ℝ ∞ (fun y => cpd j φ y) := by
  have h1 : ContDiff ℝ ∞ (fderiv ℝ φ) := ContDiff.fderiv_right (m := ∞) hφ (by simp)
  exact h1.clm_apply contDiff_const

theorem coef_cpd_per {c : ℝ} {φ : Coord → ℝ} (hφ : ∀ y, φ (qShift c y) = φ y) (j : Fin 3)
    (y : Coord) : cpd j φ (qShift c y) = cpd j φ y := by
  have hq : ∀ z : Coord, qShift c z = z + ((0 : ℝ), ((c : ℝ), (0 : ℝ))) := by
    rintro ⟨z1, z2, z3⟩
    simp [qShift]
  have hfun : (fun z : Coord => φ (z + ((0 : ℝ), ((c : ℝ), (0 : ℝ))))) = φ := by
    funext z
    have h := hφ z
    rw [hq z] at h
    exact h
  have hd : fderiv ℝ φ (y + ((0 : ℝ), ((c : ℝ), (0 : ℝ)))) = fderiv ℝ φ y := by
    have h : fderiv ℝ (fun z : Coord => φ (z + ((0 : ℝ), ((c : ℝ), (0 : ℝ))))) y =
        fderiv ℝ φ (y + ((0 : ℝ), ((c : ℝ), (0 : ℝ)))) := fderiv_comp_add_right _
    rw [hfun] at h
    exact h.symm
  unfold cpd
  rw [hq y, hd]

theorem coef_cpd_vanish {U : Set Coord} (hU : IsOpen U) {φ : Coord → ℝ}
    (h : ∀ y ∈ U, φ y = 0) (j : Fin 3) : ∀ y ∈ U, cpd j φ y = 0 := by
  intro y hy
  have hev : φ =ᶠ[𝓝 y] (fun _ : Coord => (0 : ℝ)) := by
    filter_upwards [hU.mem_nhds hy] with z hz
    exact h z hz
  have hd : fderiv ℝ φ y = fderiv ℝ (fun _ : Coord => (0 : ℝ)) y := hev.fderiv_eq
  unfold cpd
  rw [hd, fderiv_const_apply]
  simp

/-! ## The flat coefficient `flatTranspose` -/

theorem coef_flatT_per {c : ℝ} (ν : ℝ) (μ : ℂ) {Ψ : Coord → Fin 2 → ℝ}
    (hΨ : ∀ y, Ψ (qShift c y) = Ψ y) (i : Fin 2) (x : Coord) :
    flatTranspose ν μ Ψ (qShift c x) i = flatTranspose ν μ Ψ x i := by
  have hφ : ∀ y, (fun z => Ψ z i) (qShift c y) = (fun z => Ψ z i) y := by
    intro y
    show Ψ (qShift c y) i = Ψ y i
    rw [hΨ y]
  have p0 := coef_cpd_per (φ := fun z => Ψ z i) hφ 0 x
  have p1 := coef_cpd_per (φ := fun y => cpd 1 (fun z => Ψ z i) y)
    (coef_cpd_per (φ := fun z => Ψ z i) hφ 1) 1 x
  have p2 := coef_cpd_per (φ := fun y => cpd 2 (fun z => Ψ z i) y)
    (coef_cpd_per (φ := fun z => Ψ z i) hφ 2) 2 x
  have e0 : Ψ (qShift c x) i = Ψ x i := by rw [hΨ x]
  unfold flatTranspose
  rw [coef_qShift_fst, e0, p0, p1, p2]

theorem coef_flatT_vanish {U : Set Coord} (hU : IsOpen U) (ν : ℝ) (μ : ℂ)
    {Ψ : Coord → Fin 2 → ℝ} (i : Fin 2) (hΨ : ∀ y ∈ U, Ψ y i = 0) (x : Coord)
    (hx : x ∈ U) : flatTranspose ν μ Ψ x i = 0 := by
  have hφ : ∀ y ∈ U, (fun z => Ψ z i) y = 0 := fun y hy => hΨ y hy
  have c0 := coef_cpd_vanish hU (φ := fun z => Ψ z i) hφ 0 x hx
  have d1 := coef_cpd_vanish hU (φ := fun y => cpd 1 (fun z => Ψ z i) y)
    (coef_cpd_vanish hU (φ := fun z => Ψ z i) hφ 1) 1 x hx
  have d2 := coef_cpd_vanish hU (φ := fun y => cpd 2 (fun z => Ψ z i) y)
    (coef_cpd_vanish hU (φ := fun z => Ψ z i) hφ 2) 2 x hx
  unfold flatTranspose
  rw [hΨ x hx, c0, d1, d2]
  simp

theorem coef_flatT_cont (ν : ℝ) (μ : ℂ) {Ψ : Coord → Fin 2 → ℝ} (i : Fin 2)
    (hΨ : ContDiff ℝ ∞ (fun z => Ψ z i)) :
    Continuous (fun x => flatTranspose ν μ Ψ x i) := by
  have s0 : Continuous (fun x => cpd 0 (fun y => Ψ y i) x) :=
    (coef_cpd_contDiff hΨ 0).continuous
  have s1 : Continuous (fun x => cpd 1 (fun y => cpd 1 (fun z => Ψ z i) y) x) :=
    (coef_cpd_contDiff (coef_cpd_contDiff hΨ 1) 1).continuous
  have s2 : Continuous (fun x => cpd 2 (fun y => cpd 2 (fun z => Ψ z i) y) x) :=
    (coef_cpd_contDiff (coef_cpd_contDiff hΨ 2) 2).continuous
  have s3 : Continuous (fun x => Ψ x i) := hΨ.continuous
  unfold flatTranspose
  fun_prop

/-! ## Assembling a linear-in-`b` profile -/

theorem coef_combo {c σ H L : ℝ} {b : CProf} {a0 a1 G : Coord → ℂ} (hσ : 0 < σ)
    (hb : ∀ᵐ x : Coord, 0 < x.1 → b (qShift c x) = b x)
    (hbi : ∀ (R : ℝ) (i : Fin 2),
      IntegrableOn (fun x : Coord => b x i) (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) volume)
    (hG : ∀ x, G x = b x 0 * a0 x + b x 1 * a1 x)
    (hc0 : Continuous a0) (hc1 : Continuous a1)
    (hp0 : ∀ x, a0 (qShift c x) = a0 x) (hp1 : ∀ x, a1 (qShift c x) = a1 x)
    (hv0 : ∀ x : Coord, (x.1 < σ ∨ H < x.1 ∨ L < |x.2.2|) → a0 x = 0)
    (hv1 : ∀ x : Coord, (x.1 < σ ∨ H < x.1 ∨ L < |x.2.2|) → a1 x = 0) :
    (∀ᵐ x : Coord, G (qShift c x) = G x) ∧
    (∀ x : Coord, (x.1 < σ ∨ H < x.1 ∨ L < |x.2.2|) → G x = 0) ∧
    (∀ R : ℝ, IntegrableOn G (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) volume) := by
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hb] with x hx
    by_cases hx0 : 0 < x.1
    · have h0 : b (qShift c x) 0 = b x 0 := by rw [hx hx0]
      have h1 : b (qShift c x) 1 = b x 1 := by rw [hx hx0]
      rw [hG, hG, hp0 x, hp1 x, h0, h1]
    · -- off the half space both sides vanish (`s < σ`; the shift fixes `s`)
      have hxs : x.1 < σ := lt_of_le_of_lt (not_lt.1 hx0) hσ
      have hxs' : (qShift c x).1 < σ := hxs
      rw [hG, hG, hv0 x (Or.inl hxs), hv1 x (Or.inl hxs), hv0 _ (Or.inl hxs'),
        hv1 _ (Or.inl hxs')]
      simp
  · intro x hx
    rw [hG, hv0 x hx, hv1 x hx]
    simp
  · intro R
    have hK : IsCompact (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) :=
      isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    have e : G = fun x => b x 0 * a0 x + b x 1 * a1 x := funext hG
    rw [e]
    exact (IntegrableOn.mul_continuousOn (hbi R 0) hc0.continuousOn hK).add
      (IntegrableOn.mul_continuousOn (hbi R 1) hc1.continuousOn hK)

/-! ## The statement `CellStreamCoeffs` -/

theorem cellStreamCoeffs : CellStreamCoeffs := by
  unfold CellStreamCoeffs
  intro c r ν μ b ψ hc hr hbH hψs hψp σ H L hσ hψ0 k
  have hb : ∀ᵐ x : Coord, 0 < x.1 → b (qShift c x) = b x := QPerHalf.ae_imp hbH.periodic
  have hbi : ∀ (R : ℝ) (i : Fin 2),
      IntegrableOn (fun x : Coord => b x i) (Icc σ H ×ˢ (Icc (-R) R ×ˢ Icc (-L) L)) volume :=
    fun R i => hrBoxIntegrable c r b hc hr hbH σ H R L hσ i
  have hU : IsOpen (coefU σ H L) := coef_isOpen σ H L
  have hψU : ∀ y ∈ coefU σ H L, ψ y = 0 := fun y hy => hψ0 y hy
  have hψc : Continuous ψ := hψs.continuous
  -- vanishing of the derivatives of `ψ` on the open region
  have z0 : ∀ y ∈ coefU σ H L, cpd 0 ψ y = 0 := coef_cpd_vanish hU (φ := ψ) hψU 0
  have z1 : ∀ y ∈ coefU σ H L, cpd 1 ψ y = 0 := coef_cpd_vanish hU (φ := ψ) hψU 1
  have z2 : ∀ y ∈ coefU σ H L, cpd 2 ψ y = 0 := coef_cpd_vanish hU (φ := ψ) hψU 2
  have z11 : ∀ y ∈ coefU σ H L, cpd 1 (cpd 1 ψ) y = 0 :=
    coef_cpd_vanish hU (φ := cpd 1 ψ) z1 1
  have z22 : ∀ y ∈ coefU σ H L, cpd 2 (cpd 2 ψ) y = 0 :=
    coef_cpd_vanish hU (φ := cpd 2 ψ) z2 2
  have z12 : ∀ y ∈ coefU σ H L, cpd 1 (cpd 2 ψ) y = 0 :=
    coef_cpd_vanish hU (φ := cpd 2 ψ) z2 1
  -- periodicity of the derivatives of `ψ`, everywhere
  have p0 : ∀ y, cpd 0 ψ (qShift c y) = cpd 0 ψ y := coef_cpd_per (φ := ψ) hψp 0
  have p1 : ∀ y, cpd 1 ψ (qShift c y) = cpd 1 ψ y := coef_cpd_per (φ := ψ) hψp 1
  have p2 : ∀ y, cpd 2 ψ (qShift c y) = cpd 2 ψ y := coef_cpd_per (φ := ψ) hψp 2
  have p11 : ∀ y, cpd 1 (cpd 1 ψ) (qShift c y) = cpd 1 (cpd 1 ψ) y :=
    coef_cpd_per (φ := cpd 1 ψ) p1 1
  have p22 : ∀ y, cpd 2 (cpd 2 ψ) (qShift c y) = cpd 2 (cpd 2 ψ) y :=
    coef_cpd_per (φ := cpd 2 ψ) p2 2
  have p12 : ∀ y, cpd 1 (cpd 2 ψ) (qShift c y) = cpd 1 (cpd 2 ψ) y :=
    coef_cpd_per (φ := cpd 2 ψ) p2 1
  -- continuity of the derivatives of `ψ`
  have k0 : Continuous (fun x => cpd 0 ψ x) := (coef_cpd_contDiff hψs 0).continuous
  have k1 : Continuous (fun x => cpd 1 ψ x) := (coef_cpd_contDiff hψs 1).continuous
  have k2 : Continuous (fun x => cpd 2 ψ x) := (coef_cpd_contDiff hψs 2).continuous
  have k11 : Continuous (fun x => cpd 1 (cpd 1 ψ) x) :=
    (coef_cpd_contDiff (coef_cpd_contDiff hψs 1) 1).continuous
  have k22 : Continuous (fun x => cpd 2 (cpd 2 ψ) x) :=
    (coef_cpd_contDiff (coef_cpd_contDiff hψs 2) 2).continuous
  have k12 : Continuous (fun x => cpd 1 (cpd 2 ψ) x) :=
    (coef_cpd_contDiff (coef_cpd_contDiff hψs 2) 1).continuous
  -- the stream field `∇^⊥ψ`
  have hΨper : ∀ y, streamField ψ (qShift c y) = streamField ψ y := by
    intro y
    simp only [streamField, p2 y, p1 y]
  have hΨ0 : ∀ y ∈ coefU σ H L, streamField ψ y 0 = 0 := fun y hy => z2 y hy
  have hΨ1 : ∀ y ∈ coefU σ H L, streamField ψ y 1 = 0 := fun y hy => by
    show -cpd 1 ψ y = 0
    rw [z1 y hy, neg_zero]
  have hΨs0 : ContDiff ℝ ∞ (fun z => streamField ψ z 0) := coef_cpd_contDiff hψs 2
  have hΨs1 : ContDiff ℝ ∞ (fun z => streamField ψ z 1) := (coef_cpd_contDiff hψs 1).neg
  fin_cases k
  · -- `G_0`: the integrand of `FlatEqCellStream`
    exact coef_combo (G := cellG ν μ b ψ 0)
      (a0 := fun x => flatTranspose ν μ (streamField ψ) x 0)
      (a1 := fun x => flatTranspose ν μ (streamField ψ) x 1)
      hσ hb hbi
      (by intro x; simp [cellG, cellG0, Fin.sum_univ_two])
      (coef_flatT_cont ν μ (Ψ := streamField ψ) 0 hΨs0)
      (coef_flatT_cont ν μ (Ψ := streamField ψ) 1 hΨs1)
      (fun x => coef_flatT_per ν μ hΨper 0 x)
      (fun x => coef_flatT_per ν μ hΨper 1 x)
      (fun x hx => coef_flatT_vanish hU ν μ 0 hΨ0 x hx)
      (fun x hx => coef_flatT_vanish hU ν μ 1 hΨ1 x hx)
  · -- `G_1`, the coefficient of `θ'`
    exact coef_combo (G := cellG ν μ b ψ 1)
      (a0 := fun x => ((-(2 * ν * x.1 * cpd 1 (cpd 2 ψ) x) : ℝ) : ℂ))
      (a1 := fun x => -((μ - 1) * (ψ x : ℂ) - ((x.1 * cpd 0 ψ x : ℝ) : ℂ) -
        ((ν * x.1 * (cpd 1 (cpd 1 ψ) x + cpd 2 (cpd 2 ψ) x) : ℝ) : ℂ)) +
        ((2 * ν * x.1 * cpd 1 (cpd 1 ψ) x : ℝ) : ℂ))
      hσ hb hbi
      (by intro x; simp [cellG, cellG1])
      (by fun_prop) (by fun_prop)
      (fun x => by simp only [coef_qShift_fst, p12])
      (fun x => by simp only [coef_qShift_fst, hψp, p0, p11, p22])
      (fun x hx => by simp [z12 x hx])
      (fun x hx => by simp [hψ0 x hx, z0 x hx, z11 x hx, z22 x hx])
  · -- `G_2`, the coefficient of `θ''`
    exact coef_combo (G := cellG ν μ b ψ 2)
      (a0 := fun x => ((-(ν * x.1 * cpd 2 ψ x) : ℝ) : ℂ))
      (a1 := fun x => ((3 * ν * x.1 * cpd 1 ψ x : ℝ) : ℂ))
      hσ hb hbi
      (by intro x; simp [cellG, cellG2])
      (by fun_prop) (by fun_prop)
      (fun x => by simp only [coef_qShift_fst, p2])
      (fun x => by simp only [coef_qShift_fst, p1])
      (fun x hx => by simp [z2 x hx])
      (fun x hx => by simp [z1 x hx])
  · -- `G_3`, the coefficient of `θ'''`
    exact coef_combo (G := cellG ν μ b ψ 3)
      (a0 := fun _ => (0 : ℂ))
      (a1 := fun x => ((ν * x.1 * ψ x : ℝ) : ℂ))
      hσ hb hbi
      (by intro x; simp [cellG, cellG3])
      continuous_const (by fun_prop)
      (fun x => rfl)
      (fun x => by simp only [coef_qShift_fst, hψp])
      (fun x hx => rfl)
      (fun x hx => by simp [hψ0 x hx])

end UnforcedLeray.Short.IIb
