import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_inst_11

/-!
# `PartIII-b:C/inst/11/4`: `HAcMeas` from four continuity leaves

Source `the November 2 reference manuscript`
4979-4980 (`ĥ_A = √s[(h^p_A)_r e_r + ((h^p_A)_z + ε(1-𝒦)ψ^p_A) e_z]`, `𝒦 = η∂_η + 2s∂_s`),
5063-5079.  On `s > 0` the lattice sums `h^p_A`, `ψ^p_A` and the derivatives `∂_η ψ^p_A`,
`∂_s ψ^p_A` are continuous in `(s,x)` (Gaussian majorants locally uniform in `(s,x)`, `A^y` is `C^6`
on `(0,∞)` since `A` is and `χ̂_f` is `C^∞`).  Proved here: `hAcContOn_of`, `hAcMeas_of`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Leaf 1 (source 4979, 5063-5079): `(s,x) ↦ h^p_A(s,x)` is continuous on `{s > 0}`
(locally uniform Gaussian majorants for `Σ_j [V_j, A^y_mer x_j]`, `DV_j` explicit). -/
def HpAContOn (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ContinuousOn (fun p : Chart => hpA ν χf A p.1 p.2) {p : Chart | 0 < p.1}

/-- Leaf 2 (source 4980, 5063-5079): `(s,x) ↦ ψ^p_A(s,x)` is continuous on `{s > 0}`. -/
def PsipAContOn (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ContinuousOn (fun p : Chart => psipA ν χf A p.1 p.2) {p : Chart | 0 < p.1}

/-- Leaf 3 (source 4980, `η∂_η ψ^p_A` in `𝒦`): on `{s > 0}` the `η`-derivative `∂_η ψ^p_A` (a
termwise-differentiable Gaussian sum, locally uniform majorants) is a continuous function of
`(s,x)`. -/
def PsipADxContOn (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∃ E : Chart → ℝ, ContinuousOn E {p : Chart | 0 < p.1} ∧
      ∀ p : Chart, 0 < p.1 → fderiv ℝ (psipA ν χf A p.1) p.2 (ei 1) = E p

/-- Leaf 4 (source 4980, `2s∂_s ψ^p_A` in `𝒦`): on `{s > 0}` the `s`-derivative `∂_s ψ^p_A`
exists (termwise, using `A^y = χ̂_f(ν·) A` is `C^1` on `(0,∞)`) and is a continuous function of
`(s,x)`. -/
def PsipADsContOn (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ∃ D : Chart → ℝ, ContinuousOn D {p : Chart | 0 < p.1} ∧
      ∀ p : Chart, 0 < p.1 → deriv (fun s' => psipA ν χf A s' p.2) p.1 = D p

/-- The meridional vector of `hAcoef` on `{s > 0}`. -/
theorem hAcoef_eq (ν ε : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) (p : Chart) (hp : 0 < p.1) :
    hAcoef ν ε χf A p = merOf (emb ((hpA ν χf A p.1 p.2).1,
      (hpA ν χf A p.1 p.2).2 + ε * (psipA ν χf A p.1 p.2 -
        Kop (fun s' y => psipA ν χf A s' y) p.1 p.2))) := by
  unfold hAcoef hhatA
  rw [smul_smul, inv_mul_cancel₀ (Real.sqrt_pos.2 hp).ne', one_smul]

/-- Reduction of the continuity leaf of `L4.lean` to the four leaves. -/
theorem hAcContOn_of (as : ℝ) (χf : ℝ → ℝ) (h1 : HpAContOn as χf) (h2 : PsipAContOn as χf)
    (h3 : PsipADxContOn as χf) (h4 : PsipADsContOn as χf) :
    ∀ (_ : IsSourceCutoffC χf) (ν ε : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
      ContinuousOn (hAcoef ν ε χf A) {p : Chart | 0 < p.1} := by
  intro hχ ν ε hν A hA
  have c1 := h1 hχ ν hν A hA
  have c2 := h2 hχ ν hν A hA
  obtain ⟨E, hE, hEe⟩ := h3 hχ ν hν A hA
  obtain ⟨D, hD, hDe⟩ := h4 hχ ν hν A hA
  have hfst : ContinuousOn (fun p : Chart => p.1) {p : Chart | 0 < p.1} := continuousOn_fst
  have hy : ContinuousOn (fun p : Chart => p.2.2) {p : Chart | 0 < p.1} :=
    continuous_snd.comp continuous_snd |>.continuousOn
  have hK : ContinuousOn (fun p : Chart => Kop (fun s' y => psipA ν χf A s' y) p.1 p.2)
      {p : Chart | 0 < p.1} := by
    refine ((hy.mul hE).add ((continuousOn_const (c := (2:ℝ)) |>.mul hfst).mul hD)).congr ?_
    intro p hp
    simp only [Kop, hEe p (by exact hp), hDe p (by exact hp), Pi.mul_apply, Pi.add_apply]
  have hmain : ContinuousOn (fun p : Chart =>
      merOf (emb ((hpA ν χf A p.1 p.2).1, (hpA ν χf A p.1 p.2).2 +
        ε * (psipA ν χf A p.1 p.2 - Kop (fun s' y => psipA ν χf A s' y) p.1 p.2))))
      {p : Chart | 0 < p.1} := by
    have e1 : ContinuousOn (fun p : Chart => (hpA ν χf A p.1 p.2).1) {p : Chart | 0 < p.1} :=
      continuous_fst.comp_continuousOn c1
    have e2 : ContinuousOn (fun p : Chart => (hpA ν χf A p.1 p.2).2 +
        ε * (psipA ν χf A p.1 p.2 - Kop (fun s' y => psipA ν χf A s' y) p.1 p.2))
        {p : Chart | 0 < p.1} :=
      (continuous_snd.comp_continuousOn c1).add ((continuousOn_const (c := ε)).mul (c2.sub hK))
    unfold merOf emb
    simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons]
    exact (PiLp.continuous_toLp 2 (fun _ : Fin 2 => ℝ)).comp_continuousOn
      (continuousOn_pi.2 fun i => by fin_cases i <;> simp [e1, e2])
  exact hmain.congr fun p hp => hAcoef_eq ν ε χf A p hp

/-- Continuity of `hAcoef` on `{p | 0 < p.1}`. -/
def HAcContOn (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν ε : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ContinuousOn (hAcoef ν ε χf A) {p : Chart | 0 < p.1}

/-- Reduction: continuity on `{0 < p.1}` gives `AEStronglyMeasurable` for `srcMeasure`, since
`srcMeasure c` is carried by `{0 < p.1}` (`ae_srcMeasure_fst_pos`). -/
theorem hAcMeas_of_contOn (as : ℝ) (χf : ℝ → ℝ) (h : HAcContOn as χf) : HAcMeas as χf := by
  intro hχ ν ε hν A hA
  have hc := h hχ ν ε hν A hA
  have hm : MeasurableSet {p : Chart | 0 < p.1} :=
    measurableSet_lt measurable_const measurable_fst
  have hr : AEStronglyMeasurable (hAcoef ν ε χf A)
      ((srcMeasure (cOf ν)).restrict {p : Chart | 0 < p.1}) :=
    hc.aestronglyMeasurable hm
  have hae : ∀ᵐ p ∂(srcMeasure (cOf ν)), p ∈ {p : Chart | 0 < p.1} :=
    ae_srcMeasure_fst_pos (cOf ν)
  rwa [Measure.restrict_eq_self_of_ae_mem hae] at hr

/-- `HAcMeas` from the four continuity leaves. -/
theorem hAcMeas_of (as : ℝ) (χf : ℝ → ℝ) (h1 : HpAContOn as χf) (h2 : PsipAContOn as χf)
    (h3 : PsipADxContOn as χf) (h4 : PsipADsContOn as χf) : HAcMeas as χf :=
  hAcMeas_of_contOn as χf (hAcContOn_of as χf h1 h2 h3 h4)

end UnforcedLeray.Short.PartIIIb.Concrete
