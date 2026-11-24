import UnforcedLeray.Short.PartIIIb.Concrete.AffineGradPin.GradLeaf5

/-!
# `PartIII-b:C/grad/3/5`: `GradMeas` from two joint smoothness leaves

Source `the November 2 reference manuscript`
4979-4980, 5063-5079.  On the open set `{s > 0}` the lattice sums `h^p_A` (`C^1`) and `ψ^p_A`
(`C^2`) are jointly smooth in `(s, x)` (Gaussian majorants locally uniform in `(s,x)`,
`A^y` is `C^6` on `(0,∞)`).  Proved here: `gradMeas_of` (joint `C^1` regularity of the components
of `ĥ_A` gives continuity of `gradAcoef` on `{s > 0}`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set

namespace UnforcedLeray.Short.PartIIIb.Concrete

/-- Leaf A (source 4979, 5063-5079): `(s,x) ↦ h^p_A(s,x)` is `C^1` on `{s > 0}`. -/
def HpAC1 (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ContDiffOn ℝ 1 (fun p : Chart => hpA ν χf A p.1 p.2) {p : Chart | 0 < p.1}

/-- Leaf B (source 4980, 5063-5079): `(s,x) ↦ ψ^p_A(s,x)` is `C^2` on `{s > 0}`. -/
def PsipAC2 (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  IsSourceCutoffC χf → ∀ (ν : ℝ), 0 < ν → ∀ A : ℝ → Mat3, IsAffElem as A →
    ContDiffOn ℝ 2 (fun p : Chart => psipA ν χf A p.1 p.2) {p : Chart | 0 < p.1}

lemma isOpen_pos : IsOpen {p : Chart | 0 < p.1} := isOpen_lt continuous_const continuous_fst

/-- partial `x`-derivative of a jointly `C^1` function is the joint derivative. -/
lemma fderiv_x_eq (F : Chart → ℝ) (hF : ContDiffOn ℝ 1 F {p : Chart | 0 < p.1}) (p : Chart)
    (hp : 0 < p.1) (v : ℝ × ℝ) :
    fderiv ℝ (fun y : ℝ × ℝ => F (p.1, y)) p.2 v = fderiv ℝ F p (0, v) := by
  have hd : DifferentiableAt ℝ F p :=
    (hF.differentiableOn one_ne_zero).differentiableAt (isOpen_pos.mem_nhds hp)
  have h1 : HasFDerivAt (fun y : ℝ × ℝ => (p.1, y))
      ((0 : (ℝ × ℝ) →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ (ℝ × ℝ))) p.2 :=
    (hasFDerivAt_const p.1 p.2).prodMk (hasFDerivAt_id p.2)
  have h2 : HasFDerivAt F (fderiv ℝ F p) (p.1, p.2) := hd.hasFDerivAt
  have := (h2.comp p.2 h1).fderiv
  have e : (fun y : ℝ × ℝ => F (p.1, y)) = F ∘ (fun y : ℝ × ℝ => (p.1, y)) := rfl
  rw [e, this]; simp

lemma deriv_s_eq (F : Chart → ℝ) (hF : ContDiffOn ℝ 1 F {p : Chart | 0 < p.1}) (p : Chart)
    (hp : 0 < p.1) :
    deriv (fun s' : ℝ => F (s', p.2)) p.1 = fderiv ℝ F p (1, 0) := by
  have hd : DifferentiableAt ℝ F p :=
    (hF.differentiableOn one_ne_zero).differentiableAt (isOpen_pos.mem_nhds hp)
  have h1 : HasDerivAt (fun s' : ℝ => (s', p.2)) ((1 : ℝ), (0 : ℝ × ℝ)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  have h2 : HasFDerivAt F (fderiv ℝ F p) (p.1, p.2) := hd.hasFDerivAt
  exact (h2.comp_hasDerivAt p.1 h1).deriv

/-- continuity of the `x`/`s` partial derivatives of a jointly `C^1` function. -/
lemma cont_fderiv_apply (F : Chart → ℝ) (hF : ContDiffOn ℝ 1 F {p : Chart | 0 < p.1})
    (w : Chart) : ContinuousOn (fun p : Chart => fderiv ℝ F p w) {p : Chart | 0 < p.1} := by
  have := (hF.fderiv_of_isOpen (m := 0) isOpen_pos (by norm_num)).continuousOn
  exact this.clm_apply continuousOn_const

/-- `cylGrad` is continuous on `{s>0}` when the components of `u` are jointly `C^1` there. -/
lemma cylGrad_contOn (ε : ℝ) (u : ℝ → ℝ × ℝ → Vec3)
    (hu : ∀ i, ContDiffOn ℝ 1 (fun p : Chart => u p.1 p.2 i) {p : Chart | 0 < p.1}) :
    ContinuousOn (fun p : Chart => cylGrad ε u p.1 p.2) {p : Chart | 0 < p.1} := by
  have hs : ContinuousOn (fun p : Chart => Real.sqrt p.1) {p : Chart | 0 < p.1} :=
    continuous_fst.sqrt.continuousOn
  have hy : ContinuousOn (fun p : Chart => p.2.2) {p : Chart | 0 < p.1} :=
    (continuous_snd.comp continuous_snd).continuousOn
  have hf1 : ContinuousOn (fun p : Chart => p.1) {p : Chart | 0 < p.1} := continuousOn_fst
  have hc : ∀ i, ContinuousOn (fun p : Chart => u p.1 p.2 i) {p : Chart | 0 < p.1} :=
    fun i => (hu i).continuousOn
  have hdx : ∀ i (v : ℝ × ℝ), ContinuousOn
      (fun p : Chart => fderiv ℝ (chartComp u i p.1) p.2 v) {p : Chart | 0 < p.1} := by
    intro i v
    refine (cont_fderiv_apply _ (hu i) (0, v)).congr ?_
    intro p hp
    exact fderiv_x_eq _ (hu i) p hp v
  have hds : ∀ i, ContinuousOn
      (fun p : Chart => deriv (fun s' => chartComp u i s' p.2) p.1) {p : Chart | 0 < p.1} := by
    intro i
    refine (cont_fderiv_apply _ (hu i) (1, 0)).congr ?_
    intro p hp
    exact deriv_s_eq _ (hu i) p hp
  have hK : ∀ i, ContinuousOn (fun p : Chart => Kop (chartComp u i) p.1 p.2)
      {p : Chart | 0 < p.1} := by
    intro i
    unfold Kop
    exact (hy.mul (hdx i (ei 1))).add ((continuousOn_const.mul hf1).mul (hds i))
  have hDr : ∀ i, ContinuousOn (fun p : Chart => physDr ε (chartComp u i) p.1 p.2)
      {p : Chart | 0 < p.1} := by
    intro i
    unfold physDr dQ
    exact hs.mul ((hdx i (ei 0)).sub (continuousOn_const.mul (hK i)))
  have hDz : ∀ i, ContinuousOn (fun p : Chart => physDz (chartComp u i) p.1 p.2)
      {p : Chart | 0 < p.1} := by
    intro i
    unfold physDz dEta
    exact hs.mul (hdx i (ei 1))
  refine continuousOn_pi.2 fun a => continuousOn_pi.2 fun b => ?_
  fin_cases a <;> fin_cases b
  · exact hDr 0
  · exact ((continuousOn_const.mul hs).mul (hc 1)).neg
  · exact hDz 0
  · exact hDr 1
  · exact (continuousOn_const.mul hs).mul (hc 0)
  · exact hDz 1
  · exact hDr 2
  · exact continuousOn_const
  · exact hDz 2

lemma continuous_matTen : Continuous matTen := by
  unfold matTen
  exact (PiLp.continuous_toLp 2 (fun _ : Fin 3 × Fin 3 => ℝ)).comp
    (continuous_pi fun ab => (continuous_apply ab.2).comp (continuous_apply ab.1))

theorem gradMeas_of (as : ℝ) (χf : ℝ → ℝ) (h1 : HpAC1 as χf) (h2 : PsipAC2 as χf) :
    GradMeas as χf := by
  refine gradMeas_of_contOn as χf ?_
  intro hχ ν ε hν A hA
  have a1 := h1 hχ ν hν A hA
  have a2 := h2 hχ ν hν A hA
  set U : Set Chart := {p : Chart | 0 < p.1} with hU
  set P : Chart → ℝ := fun p => psipA ν χf A p.1 p.2 with hP
  have hK : ContDiffOn ℝ 1 (fun p : Chart => Kop (fun s' y => psipA ν χf A s' y) p.1 p.2) U := by
    have hd : ContDiffOn ℝ 1 (fun p : Chart => fderiv ℝ P p) U :=
      a2.fderiv_of_isOpen isOpen_pos (by norm_num)
    have e1 : ContDiffOn ℝ 1 (fun p : Chart => fderiv ℝ P p (0, ei 1)) U :=
      hd.clm_apply contDiffOn_const
    have e2 : ContDiffOn ℝ 1 (fun p : Chart => fderiv ℝ P p (1, 0)) U :=
      hd.clm_apply contDiffOn_const
    have a2' : ContDiffOn ℝ 1 P U := a2.of_le (by norm_num)
    have hy : ContDiffOn ℝ 1 (fun p : Chart => p.2.2) U :=
      (contDiff_snd.comp contDiff_snd).contDiffOn
    refine ((hy.mul e1).add
      (((contDiffOn_const (c := (2:ℝ))).mul contDiff_fst.contDiffOn).mul e2)).congr ?_
    intro p hp
    simp only [Kop]
    rw [fderiv_x_eq P a2' p hp (ei 1), deriv_s_eq P a2' p hp]
  have hsq : ContDiffOn ℝ 1 (fun p : Chart => Real.sqrt p.1) U := by
    intro p hp
    exact ((Real.contDiffAt_sqrt (ne_of_gt hp)).comp p contDiffAt_fst).contDiffWithinAt
  have hP1 : ContDiffOn ℝ 1 P U := a2.of_le (by norm_num)
  have c1 : ContDiffOn ℝ 1 (fun p : Chart => (hpA ν χf A p.1 p.2).1) U :=
    contDiff_fst.comp_contDiffOn a1
  have c2 : ContDiffOn ℝ 1 (fun p : Chart => (hpA ν χf A p.1 p.2).2) U :=
    contDiff_snd.comp_contDiffOn a1
  have hu : ∀ i, ContDiffOn ℝ 1 (fun p : Chart => hhatA ν ε χf A p.1 p.2 i) U := by
    intro i
    fin_cases i
    · simp only [hhatA, emb]
      simpa using hsq.mul c1
    · simp [hhatA, emb]
      exact contDiffOn_const
    · simp only [hhatA, emb]
      simpa using hsq.mul (c2.add (contDiffOn_const.mul (hP1.sub hK)))
  have hcg := cylGrad_contOn ε (hhatA ν ε χf A) hu
  have hinv : ContinuousOn (fun p : Chart => (p.1)⁻¹) U :=
    continuousOn_fst.inv₀ fun p hp => ne_of_gt hp
  have := hinv.smul (continuous_matTen.comp_continuousOn hcg)
  exact this

end UnforcedLeray.Short.PartIIIb.Concrete
