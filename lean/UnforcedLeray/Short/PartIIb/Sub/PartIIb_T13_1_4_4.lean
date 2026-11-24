import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T13_1_4

/-!
# Part II-b, task `PartII-b:T13/1/4/4` (`ChmLimit`): decomposition

Source of record: `the November 2 reference manuscript` (SP) lines 1933-1935
("applying the Euclidean estimate to a cutoff of `N` repeated cells ... letting `N → ∞`") and the
Euclidean estimate SP 1377-1424.

Passage to the limit: apply the a priori inequality to the differences `w n - w m`; the derivatives
are Cauchy in `L^r(cylMeas c)`, converge to periodic measurable limits, the weak identities pass to
the limit by integration by parts and the local bound on periodic pairings, the bounds by norm
convergence.

NOTE. Without a measurability hypothesis on `f` the statement would be false (the
lower-integral norm `eLpNorm` of a non-null-measurable `f` does not satisfy the triangle
inequality; e.g. `f = g · 1_V`, `V` a Bernstein set, gives `‖g - f‖ = ‖f‖ = 0`). `ChmLimit`
therefore carries `AEStronglyMeasurable f volume`, available at the only use (`cylHeatMaxReg_of`,
hypothesis `hfm`); `ChmLimitM` is an alias of `ChmLimit`.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- `ChmLimit` (which now carries the measurability of `f`). Kept as an alias. -/
def ChmLimitM : Prop := ChmLimit

/-- **Leaf 1 (linearity on nice functions, SP 1933-1935).** For `ChmNice` functions the difference
is `ChmNice`, and the first and second spatial derivatives and `chmRhs ν` are additive (smooth
functions are differentiable). -/
def ChmSubLin : Prop :=
  ∀ r c : ℝ, 1 < r → ∀ w w' : Coord → ℂ, ChmNice c r w → ChmNice c r w' →
    ChmNice c r (fun x => w x - w' x) ∧
    (∀ j, cdv j (fun x => w x - w' x) = fun x => cdv j w x - cdv j w' x) ∧
    (∀ i j, cdv i (cdv j (fun x => w x - w' x)) =
      fun x => cdv i (cdv j w) x - cdv i (cdv j w') x) ∧
    ∀ ν, chmRhs ν (fun x => w x - w' x) = fun x => chmRhs ν w x - chmRhs ν w' x

/-- **Leaf 2 (derivatives of smooth periodic functions are smooth periodic).** `cdv j w` is smooth
and `qShift c`-invariant when `w` is (the derivative commutes with the translation `qShift c`). -/
def ChmDerivPer : Prop :=
  ∀ (c : ℝ) (w : Coord → ℂ), ContDiff ℝ ∞ w → (∀ x, w (qShift c x) = w x) →
    ∀ j, ContDiff ℝ ∞ (cdv j w) ∧ ∀ x, cdv j w (qShift c x) = cdv j w x

/-- **Leaf 3 (completeness of periodic `L^r(cylMeas c)`, SP 1933-1935).** A sequence of continuous
`q`-periodic functions with finite norm which is Cauchy in the form `‖g n - g m‖ ≤ a n + a m`,
`a n → 0`, converges in `L^r(cylMeas c)` to a `q`-periodic function that is measurable for
`volume` (Mathlib `MeasureTheory.Lp` completeness on the cell, then periodic extension of an
a.e.-convergent subsequence's limit). -/
def ChmCauchyPer : Prop :=
  ∀ r c : ℝ, 1 < r → 0 < c → ∀ g : ℕ → Coord → ℂ,
    (∀ n, Continuous (g n) ∧ (∀ x, g n (qShift c x) = g n x) ∧ cylNorm c r (g n) < ⊤) →
    ∀ a : ℕ → ℝ≥0∞, Tendsto a atTop (𝓝 0) →
    (∀ n m, cylNorm c r (fun x => g n x - g m x) ≤ a n + a m) →
    ∃ G : Coord → ℂ, QPeriodicS c G ∧ AEStronglyMeasurable G volume ∧
      Tendsto (fun n => cylNorm c r (fun x => g n x - G x)) atTop (𝓝 0)

/-- **Leaf 4 (local bound for periodic pairings, SP 1933-1935).** For a continuous compactly
supported real `ψ`, `L^r(cylMeas c)`-convergence of `q`-periodic measurable functions with finite
norm implies convergence of the pairings `∫ g n ψ → ∫ h ψ` (`|∫ g ψ| ≤ C_ψ ‖g‖_{L^r(cylMeas c)}`
for `q`-periodic `g`: `supp ψ` meets finitely many cells; periodicity moves each to the base cell;
Hölder). -/
def ChmPairLim : Prop :=
  ∀ r c : ℝ, 1 < r → 0 < c → ∀ ψ : Coord → ℝ, Continuous ψ → HasCompactSupport ψ →
    ∀ (g : ℕ → Coord → ℂ) (h : Coord → ℂ),
      (∀ n, QPeriodicS c (g n)) → QPeriodicS c h →
      (∀ n, AEStronglyMeasurable (g n) volume) → AEStronglyMeasurable h volume →
      (∀ n, cylNorm c r (g n) < ⊤) → cylNorm c r h < ⊤ →
      Tendsto (fun n => cylNorm c r (fun x => g n x - h x)) atTop (𝓝 0) →
      Tendsto (fun n => ∫ x, g n x * (ψ x : ℂ)) atTop (𝓝 (∫ x, h x * (ψ x : ℂ)))

/-- **Leaf 5 (integration by parts on `Coord`).** For smooth `w` and a test `φ`:
`∫ w ∂_s φ = -∫ ∂_s w φ` and `∫ w ∂_i∂_j φ = ∫ ∂_i∂_j w φ` (`i, j ∈ {q, η}`; symmetry of second
derivatives of smooth functions). -/
def ChmIBP : Prop :=
  ∀ w : Coord → ℂ, ContDiff ℝ ∞ w → ∀ φ : Coord → ℝ, IsSTTestCoord φ →
    (∫ x, w x * (cpd 0 φ x : ℂ) = -∫ x, cdv 0 w x * (φ x : ℂ)) ∧
    ∀ i j : Fin 2, ∫ x, w x * (cpd i.succ (fun y => cpd j.succ φ y) x : ℂ) =
      ∫ x, cdv i.succ (cdv j.succ w) x * (φ x : ℂ)

/-- **Leaf 6 (derivatives of a test are tests).** If `φ` is a space-time test then so is `cpd j φ`. -/
def ChmTestDeriv : Prop :=
  ∀ (φ : Coord → ℝ) (j : Fin 3), IsSTTestCoord φ → IsSTTestCoord (cpd j φ)


private lemma chm_cylMeas_ac (c : ℝ) : cylMeas c ≪ (volume : Measure Coord) := by
  have h1 : UnforcedLeray.Cyl.avgμ c ≪ (volume : Measure (ℝ × ℝ)) := by
    unfold UnforcedLeray.Cyl.avgμ UnforcedLeray.Cyl.cellμ
    intro s hs
    have h0 : (volume.restrict (UnforcedLeray.Cyl.cell c)) s = 0 :=
      le_antisymm ((Measure.restrict_le_self s).trans hs.le) bot_le
    simp [h0]
  exact Measure.AbsolutelyContinuous.prod Measure.AbsolutelyContinuous.rfl h1

lemma chm_enorm_mul (c r ν : ℝ) (hν : 0 < ν) (h : Coord → ℂ) :
    cylNorm c r (fun x => (ν : ℂ) * h x) = ENNReal.ofReal ν * cylNorm c r h := by
  have := eLpNorm_const_smul (μ := cylMeas c) (p := ENNReal.ofReal r) (ν : ℂ) h
  unfold cylNorm
  rw [show (fun x => (ν : ℂ) * h x) = (ν : ℂ) • h from rfl, this]
  congr 1
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hν]


lemma chm_limit_bound (μ : Measure Coord) (p : ℝ≥0∞) (hp1 : 1 ≤ p) (K : ℝ≥0∞)
    (g R : ℕ → Coord → ℂ) (G f : Coord → ℂ)
    (hgm : ∀ n, AEStronglyMeasurable (g n) μ) (hGm : AEStronglyMeasurable G μ)
    (hRm : ∀ n, AEStronglyMeasurable (R n) μ) (hfm : AEStronglyMeasurable f μ)
    (hb : ∀ n, eLpNorm (g n) p μ ≤ K * eLpNorm (R n) p μ)
    (h1 : Tendsto (fun n => eLpNorm (fun x => g n x - G x) p μ) atTop (𝓝 0))
    (h2 : Tendsto (fun n => eLpNorm (fun x => R n x - f x) p μ) atTop (𝓝 0)) (hK : K ≠ ⊤) :
    eLpNorm G p μ ≤ K * eLpNorm f p μ := by
  have hlim : Tendsto (fun n => eLpNorm (fun x => g n x - G x) p μ +
      K * (eLpNorm (fun x => R n x - f x) p μ + eLpNorm f p μ)) atTop
      (𝓝 (0 + K * (0 + eLpNorm f p μ))) :=
    h1.add (ENNReal.Tendsto.const_mul (h2.add_const _) (Or.inr hK))
  simp only [zero_add] at hlim
  refine ge_of_tendsto' hlim (fun n => ?_)
  have hneg : ∀ n, eLpNorm (fun x => -(g n x - G x)) p μ = eLpNorm (fun x => g n x - G x) p μ :=
    fun n => eLpNorm_neg (fun x => g n x - G x) p μ
  have e1 : eLpNorm G p μ ≤ eLpNorm (fun x => g n x - G x) p μ + eLpNorm (g n) p μ := by
    have : G = fun x => -(g n x - G x) + g n x := by funext x; ring
    calc eLpNorm G p μ = eLpNorm (fun x => -(g n x - G x) + g n x) p μ := by rw [← this]
      _ ≤ eLpNorm (fun x => -(g n x - G x)) p μ + eLpNorm (g n) p μ :=
          eLpNorm_add_le ((hgm n).sub hGm).neg (hgm n) hp1
      _ = _ := by rw [hneg n]
  have e2 : eLpNorm (R n) p μ ≤ eLpNorm (fun x => R n x - f x) p μ + eLpNorm f p μ := by
    have : R n = fun x => (R n x - f x) + f x := by funext x; ring
    calc eLpNorm (R n) p μ = eLpNorm (fun x => (R n x - f x) + f x) p μ := by rw [← this]
      _ ≤ _ := eLpNorm_add_le ((hRm n).sub hfm) hfm hp1
  calc eLpNorm G p μ ≤ eLpNorm (fun x => g n x - G x) p μ + eLpNorm (g n) p μ := e1
    _ ≤ eLpNorm (fun x => g n x - G x) p μ + K * eLpNorm (R n) p μ := by gcongr; exact hb n
    _ ≤ _ := by gcongr

lemma chm_limit_fin (μ : Measure Coord) (p : ℝ≥0∞) (hp1 : 1 ≤ p)
    (g : ℕ → Coord → ℂ) (G : Coord → ℂ)
    (hgm : ∀ n, AEStronglyMeasurable (g n) μ) (hGm : AEStronglyMeasurable G μ)
    (hfin : ∀ n, eLpNorm (g n) p μ < ⊤)
    (h1 : Tendsto (fun n => eLpNorm (fun x => g n x - G x) p μ) atTop (𝓝 0)) :
    eLpNorm G p μ < ⊤ := by
  obtain ⟨n, hn⟩ := (h1.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ≥0∞) < 1))).exists
  have : G = fun x => -(g n x - G x) + g n x := by funext x; ring
  calc eLpNorm G p μ = eLpNorm (fun x => -(g n x - G x) + g n x) p μ := by rw [← this]
    _ ≤ eLpNorm (fun x => -(g n x - G x)) p μ + eLpNorm (g n) p μ :=
        eLpNorm_add_le ((hgm n).sub hGm).neg (hgm n) hp1
    _ < ⊤ := by
        rw [show eLpNorm (fun x => -(g n x - G x)) p μ = eLpNorm (fun x => g n x - G x) p μ from
          eLpNorm_neg (fun x => g n x - G x) p μ]
        exact ENNReal.add_lt_top.2 ⟨hn.trans ENNReal.one_lt_top, hfin n⟩


theorem chmLimitM_of (hS : ChmSubLin) (hD : ChmDerivPer) (hC : ChmCauchyPer) (hP : ChmPairLim)
    (hI : ChmIBP) (hT : ChmTestDeriv) : ChmLimitM := by
  show ChmLimit
  intro r hr c C ν hc hCp hν hA u f hup hum hfm w hw
  obtain ⟨hnice, hrnice, hwu, hrf⟩ := hw
  have hac := chm_cylMeas_ac c
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal r := by
    simpa using ENNReal.ofReal_le_ofReal hr.le
  have mono : ∀ g : Coord → ℂ, AEStronglyMeasurable g volume →
      AEStronglyMeasurable g (cylMeas c) := fun g hg => hg.mono_ac hac
  have cmeas : ∀ g : Coord → ℂ, Continuous g → AEStronglyMeasurable g (cylMeas c) :=
    fun g hg => hg.aestronglyMeasurable
  have hRc : ∀ n, Continuous (chmRhs ν (w n)) := fun n => (hrnice n).smooth.continuous
  have hwc : ∀ n, Continuous (w n) := fun n => (hnice n).smooth.continuous
  have hfmc := mono f hfm
  have humc := mono u hum
  have hper : ∀ n j, ContDiff ℝ ∞ (cdv j (w n)) ∧ ∀ x, cdv j (w n) (qShift c x) = cdv j (w n) x :=
    fun n j => hD c (w n) (hnice n).smooth (hnice n).periodic j
  have hper2 : ∀ n i j, ContDiff ℝ ∞ (cdv i (cdv j (w n))) ∧
      ∀ x, cdv i (cdv j (w n)) (qShift c x) = cdv i (cdv j (w n)) x :=
    fun n i j => hD c _ (hper n j).1 (hper n j).2 i
  -- the errors
  obtain ⟨e, he⟩ : ∃ e : ℕ → ℝ≥0∞, e = fun n => cylNorm c r (fun x => chmRhs ν (w n) x - f x) :=
    ⟨_, rfl⟩
  have he0 : Tendsto e atTop (𝓝 0) := by rw [he]; exact hrf
  have hmeas_Rf : ∀ n, AEStronglyMeasurable (fun x => chmRhs ν (w n) x - f x) (cylMeas c) :=
    fun n => (cmeas _ (hRc n)).sub hfmc
  have hRdiff : ∀ n m, cylNorm c r (fun x => chmRhs ν (w n) x - chmRhs ν (w m) x) ≤ e n + e m := by
    intro n m
    have : (fun x => chmRhs ν (w n) x - chmRhs ν (w m) x) =
        fun x => (chmRhs ν (w n) x - f x) - (chmRhs ν (w m) x - f x) := by funext x; ring
    rw [he]
    unfold cylNorm; rw [this]
    exact eLpNorm_sub_le (hmeas_Rf n) (hmeas_Rf m) hp1
  have hsub := fun n m => hS r c hr (w n) (w m) (hnice n) (hnice m)
  have hbd0 : ∀ n m, cylNorm c r (fun x => cdv 0 (w n) x - cdv 0 (w m) x) ≤
      ENNReal.ofReal C * (e n + e m) := by
    intro n m
    obtain ⟨hN, h1, h2, h3⟩ := hsub n m
    have := (hA _ hN).1
    rw [h1 0, h3 ν] at this
    exact this.trans (by gcongr; exact hRdiff n m)
  have hbd2 : ∀ i j : Fin 2, ∀ n m,
      cylNorm c r (fun x => cdv i.succ (cdv j.succ (w n)) x - cdv i.succ (cdv j.succ (w m)) x) ≤
        ENNReal.ofReal (ν⁻¹ * C) * (e n + e m) := by
    intro i j n m
    obtain ⟨hN, h1, h2, h3⟩ := hsub n m
    have h := (hA _ hN).2 i j
    rw [h2 i.succ j.succ, h3 ν] at h
    have e1 : cylNorm c r (fun x => (ν : ℂ) * (cdv i.succ (cdv j.succ (w n)) x -
        cdv i.succ (cdv j.succ (w m)) x)) = ENNReal.ofReal ν *
        cylNorm c r (fun x => cdv i.succ (cdv j.succ (w n)) x - cdv i.succ (cdv j.succ (w m)) x) :=
      chm_enorm_mul c r ν hν _
    have h' : (fun x => (ν : ℂ) * (cdv i.succ (cdv j.succ (w n)) x -
        cdv i.succ (cdv j.succ (w m)) x)) = fun x => (ν : ℂ) * (fun x => cdv i.succ (cdv j.succ (w n)) x -
        cdv i.succ (cdv j.succ (w m)) x) x := rfl
    set X := cylNorm c r (fun x => cdv i.succ (cdv j.succ (w n)) x -
        cdv i.succ (cdv j.succ (w m)) x) with hX
    have h2' : ENNReal.ofReal ν * X ≤ ENNReal.ofReal C * (e n + e m) := by
      refine le_trans ?_ (le_trans h (by gcongr; exact hRdiff n m))
      exact e1.symm.le
    have hinv : ENNReal.ofReal ν⁻¹ * ENNReal.ofReal ν = 1 := by
      rw [← ENNReal.ofReal_mul (inv_nonneg.2 hν.le), inv_mul_cancel₀ hν.ne', ENNReal.ofReal_one]
    calc X = ENNReal.ofReal ν⁻¹ * (ENNReal.ofReal ν * X) := by rw [← mul_assoc, hinv, one_mul]
      _ ≤ ENNReal.ofReal ν⁻¹ * (ENNReal.ofReal C * (e n + e m)) := by gcongr
      _ = _ := by rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_nonneg.2 hν.le)]
  -- Dt
  obtain ⟨Dt, hDtp, hDtm, hDtt⟩ := hC r c hr hc (fun n => cdv 0 (w n))
    (fun n => ⟨(hper n 0).1.continuous, (hper n 0).2, (hnice n).mem1 0⟩)
    (fun n => ENNReal.ofReal C * e n)
    (by have := ENNReal.Tendsto.const_mul he0 (Or.inr (ENNReal.ofReal_ne_top (r := C)))
        simpa using this)
    (fun n m => (hbd0 n m).trans (by rw [mul_add]))
  have hD2 : ∀ i j : Fin 2, ∃ G : Coord → ℂ, QPeriodicS c G ∧ AEStronglyMeasurable G volume ∧
      Tendsto (fun n => cylNorm c r (fun x => cdv i.succ (cdv j.succ (w n)) x - G x)) atTop (𝓝 0) :=
    fun i j => hC r c hr hc (fun n => cdv i.succ (cdv j.succ (w n)))
      (fun n => ⟨(hper2 n _ _).1.continuous, (hper2 n _ _).2, (hnice n).mem2 _ _⟩)
      (fun n => ENNReal.ofReal (ν⁻¹ * C) * e n)
      (by have := ENNReal.Tendsto.const_mul he0 (Or.inr (ENNReal.ofReal_ne_top (r := ν⁻¹ * C)))
          simpa using this)
      (fun n m => (hbd2 i j n m).trans (by rw [mul_add]))
  choose D2 hD2p hD2m hD2t using hD2
  -- measurability / finiteness
  have hDtmc := mono Dt hDtm
  have hD2mc := fun i j => mono (D2 i j) (hD2m i j)
  have hfin_f : cylNorm c r f < ⊤ :=
    chm_limit_fin (cylMeas c) _ hp1 (fun n => chmRhs ν (w n)) f (fun n => cmeas _ (hRc n)) hfmc
      (fun n => (hrnice n).mem0) hrf
  have hfin_u : cylNorm c r u < ⊤ :=
    chm_limit_fin (cylMeas c) _ hp1 w u (fun n => cmeas _ (hwc n)) humc (fun n => (hnice n).mem0) hwu
  have hDt_b : cylNorm c r Dt ≤ ENNReal.ofReal C * cylNorm c r f :=
    chm_limit_bound (cylMeas c) _ hp1 _ (fun n => cdv 0 (w n)) (fun n => chmRhs ν (w n)) Dt f
      (fun n => cmeas _ (hper n 0).1.continuous) hDtmc (fun n => cmeas _ (hRc n)) hfmc
      (fun n => (hA _ (hnice n)).1) hDtt hrf ENNReal.ofReal_ne_top
  have hDt_fin : cylNorm c r Dt < ⊤ :=
    hDt_b.trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin_f)
  have hD2_b : ∀ i j, cylNorm c r (fun x => (ν : ℂ) * D2 i j x) ≤
      ENNReal.ofReal C * cylNorm c r f := by
    intro i j
    refine chm_limit_bound (cylMeas c) _ hp1 _
      (fun n x => (ν : ℂ) * cdv i.succ (cdv j.succ (w n)) x) (fun n => chmRhs ν (w n))
      (fun x => (ν : ℂ) * D2 i j x) f
      (fun n => cmeas _ (continuous_const.mul (hper2 n _ _).1.continuous)) (aestronglyMeasurable_const.mul (hD2mc i j))
      (fun n => cmeas _ (hRc n)) hfmc (fun n => (hA _ (hnice n)).2 i j) ?_ hrf ENNReal.ofReal_ne_top
    have := (ENNReal.Tendsto.const_mul (hD2t i j) (Or.inr (ENNReal.ofReal_ne_top (r := ν)))).congr
      (fun n => (chm_enorm_mul c r ν hν (fun x => cdv i.succ (cdv j.succ (w n)) x - D2 i j x)).symm)
    simpa [mul_sub] using this
  have hD2_fin : ∀ i j, cylNorm c r (D2 i j) < ⊤ := by
    intro i j
    have h1 := (hD2_b i j).trans_lt (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin_f)
    rw [chm_enorm_mul c r ν hν] at h1
    rcases ENNReal.mul_lt_top_iff.1 h1 with h | h | h
    · exact h.2
    · exact absurd h (by simpa using hν)
    · rw [h]; exact ENNReal.zero_lt_top
  have hwper : ∀ n, QPeriodicS c (w n) := fun n => Filter.Eventually.of_forall (hnice n).periodic
  have hwmv : ∀ n, AEStronglyMeasurable (w n) volume := fun n => (hwc n).aestronglyMeasurable
  have hgper : ∀ n j, QPeriodicS c (cdv j (w n)) :=
    fun n j => Filter.Eventually.of_forall (hper n j).2
  have hgmv : ∀ n j, AEStronglyMeasurable (cdv j (w n)) volume :=
    fun n j => (hper n j).1.continuous.aestronglyMeasurable
  have hg2per : ∀ n i j, QPeriodicS c (cdv i (cdv j (w n))) :=
    fun n i j => Filter.Eventually.of_forall (hper2 n i j).2
  have hg2mv : ∀ n i j, AEStronglyMeasurable (cdv i (cdv j (w n))) volume :=
    fun n i j => (hper2 n i j).1.continuous.aestronglyMeasurable
  have tst : ∀ φ : Coord → ℝ, IsSTTestCoord φ → Continuous φ ∧ HasCompactSupport φ :=
    fun φ hφ => ⟨hφ.smooth.continuous, hφ.compact⟩
  refine ⟨Dt, D2, ⟨hDtp, hDtm⟩, fun i j => ⟨hD2p i j, hD2m i j⟩, ?_, ?_, hDt_b, hD2_b⟩
  · intro φ hφ
    have t1 := hP r c hr hc (cpd 0 φ) (tst _ (hT φ 0 hφ)).1 (tst _ (hT φ 0 hφ)).2 w u hwper hup
      hwmv hum (fun n => (hnice n).mem0) hfin_u hwu
    have t2 := hP r c hr hc φ (tst φ hφ).1 (tst φ hφ).2 (fun n => cdv 0 (w n)) Dt
      (fun n => hgper n 0) hDtp (fun n => hgmv n 0) hDtm (fun n => (hnice n).mem1 0) hDt_fin hDtt
    have heq : (fun n => ∫ x, w n x * (cpd 0 φ x : ℂ)) =
        fun n => -∫ x, cdv 0 (w n) x * (φ x : ℂ) :=
      funext fun n => (hI (w n) (hnice n).smooth φ hφ).1
    rw [heq] at t1
    exact tendsto_nhds_unique t1 t2.neg
  · intro i j φ hφ
    have hψ := hT (fun y => cpd j.succ φ y) i.succ (hT φ j.succ hφ)
    have t1 := hP r c hr hc _ (tst _ hψ).1 (tst _ hψ).2 w u hwper hup
      hwmv hum (fun n => (hnice n).mem0) hfin_u hwu
    have t2 := hP r c hr hc φ (tst φ hφ).1 (tst φ hφ).2
      (fun n => cdv i.succ (cdv j.succ (w n))) (D2 i j)
      (fun n => hg2per n _ _) (hD2p i j) (fun n => hg2mv n _ _) (hD2m i j)
      (fun n => (hnice n).mem2 _ _) (hD2_fin i j) (hD2t i j)
    have heq : (fun n => ∫ x, w n x * (cpd i.succ (fun y => cpd j.succ φ y) x : ℂ)) =
        fun n => ∫ x, cdv i.succ (cdv j.succ (w n)) x * (φ x : ℂ) :=
      funext fun n => (hI (w n) (hnice n).smooth φ hφ).2 i j
    rw [heq] at t1
    exact tendsto_nhds_unique t1 t2


theorem chmTestDeriv : ChmTestDeriv := by
  intro φ j hφ
  refine ⟨?_, ?_⟩
  · exact (hφ.smooth.fderiv_right (m := ∞) le_rfl).clm_apply contDiff_const
  · exact hφ.compact.fderiv_apply ℝ (cdir j)

end UnforcedLeray.Short.IIb
