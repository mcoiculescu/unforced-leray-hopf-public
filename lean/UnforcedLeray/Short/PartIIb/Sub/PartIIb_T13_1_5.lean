import UnforcedLeray.Short.PartIIb.Tasks.FlatWindows.Org.FlatGraphOrg

/-!
# Part II-b, task `PartII-b:T13/1/5` (`CylGradInterp`): decomposition

Source of record: `the November 2 reference manuscript` lines 1932-1933
("interpolation gives its gradient bound"), with the period-free mechanism of lines 1933-1935.

Proof of `CylGradInterp`: (A) the a priori inequality for smooth `q`-periodic functions
(`CgiApriori`: one-dimensional interpolation along each line, then Fubini); (B) smooth periodic
approximation of `(u, D2)` (`CgiMollify`); (C) passage to the limit (`CgiLimit`), which uses (A)
only for the differences of the approximants.
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.IIb

open MeasureTheory Set Filter
open scoped ENNReal ContDiff Topology

/-- Spatial partial derivative `∂_j w` (`j = 0, 1, 2` for `s, q, η`) of a complex function. -/
def cdv (j : Fin 3) (w : Coord → ℂ) (x : Coord) : ℂ := fderiv ℝ w x (cdir j)

/-- The `L^r(cylMeas c)` norm. -/
abbrev cylNorm (c r : ℝ) (f : Coord → ℂ) : ℝ≥0∞ := eLpNorm f (ENNReal.ofReal r) (cylMeas c)

/-- The right-hand side `C (λ⁻¹ ‖u‖ + λ Σ_{k,l} ‖D2 k l‖)` of the interpolation inequality. -/
def cgiRhs (c r C lam : ℝ) (u : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal C * (ENNReal.ofReal lam⁻¹ * cylNorm c r u +
    ENNReal.ofReal lam * ∑ k : Fin 2, ∑ l : Fin 2, cylNorm c r (D2 k l))

/-- A smooth `q`-periodic function with `w`, `∂_i w`, `∂_k∂_l w` (spatial) in `L^r(cylMeas c)`. -/
structure CgiNice (c r : ℝ) (w : Coord → ℂ) : Prop where
  smooth : ContDiff ℝ ∞ w
  periodic : ∀ x, w (qShift c x) = w x
  mem0 : cylNorm c r w < ⊤
  mem1 : ∀ i : Fin 2, cylNorm c r (cdv i.succ w) < ⊤
  mem2 : ∀ k l : Fin 2, cylNorm c r (cdv k.succ (cdv l.succ w)) < ⊤

/-- **Leaf (1-D interpolation on a line, SP 1932).** For `g ∈ C²(ℝ; ℂ)` with `g, g'' ∈ L^r(ℝ)`:
`‖g'‖_r ≤ C (λ⁻¹ ‖g‖_r + λ ‖g''‖_r)` for all `λ > 0`, `C` depending only on `r`. -/
def LineInterpR : Prop :=
  ∀ r : ℝ, 1 < r → ∃ C : ℝ, 0 < C ∧ ∀ g : ℝ → ℂ, ContDiff ℝ 2 g →
    eLpNorm g (ENNReal.ofReal r) volume < ⊤ →
    eLpNorm (deriv (deriv g)) (ENNReal.ofReal r) volume < ⊤ →
    ∀ lam : ℝ, 0 < lam → eLpNorm (deriv g) (ENNReal.ofReal r) volume ≤
      ENNReal.ofReal C * (ENNReal.ofReal lam⁻¹ * eLpNorm g (ENNReal.ofReal r) volume +
        ENNReal.ofReal lam * eLpNorm (deriv (deriv g)) (ENNReal.ofReal r) volume)

/-- **Leaf (1-D interpolation, periodic case, no period loss, SP 1932-1935).** For a `C²`
`c`-periodic `g : ℝ → ℂ` and the cell `[-c/2, c/2)` (Lebesgue measure), for all `λ > 0` (also
`λ ≥ c`, where `g'` has mean zero over a period) `‖g'‖_r ≤ C (λ⁻¹ ‖g‖_r + λ ‖g''‖_r)` with `C`
depending only on `r`, not on `c`. -/
def LineInterpPer : Prop :=
  ∀ r : ℝ, 1 < r → ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∀ g : ℝ → ℂ, ContDiff ℝ 2 g →
    (∀ t, g (t + c) = g t) →
    ∀ lam : ℝ, 0 < lam →
      eLpNorm (deriv g) (ENNReal.ofReal r) (volume.restrict (Ico (-c / 2) (c / 2))) ≤
      ENNReal.ofReal C *
        (ENNReal.ofReal lam⁻¹ * eLpNorm g (ENNReal.ofReal r) (volume.restrict (Ico (-c / 2) (c / 2))) +
        ENNReal.ofReal lam *
          eLpNorm (deriv (deriv g)) (ENNReal.ofReal r) (volume.restrict (Ico (-c / 2) (c / 2))))

/-- **Leaf (A, `η` direction).** Slice-wise (`s`, `q` fixed, line in `η`) `LineInterpR`, then
Minkowski/Fubini over `cylMeas c`: for nice `w`, `‖∂_η w‖ ≤ C (λ⁻¹‖w‖ + λ ‖∂_η² w‖)`. -/
def CgiAprioriEta : Prop :=
  ∀ r : ℝ, 1 < r → ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∀ w : Coord → ℂ, CgiNice c r w →
    ∀ lam : ℝ, 0 < lam → cylNorm c r (cdv 2 w) ≤
      ENNReal.ofReal C * (ENNReal.ofReal lam⁻¹ * cylNorm c r w +
        ENNReal.ofReal lam * cylNorm c r (cdv 2 (cdv 2 w)))

/-- **Leaf (A, `q` direction).** Slice-wise (`s`, `η` fixed, line in `q`) `LineInterpPer`, then
Fubini over `cylMeas c` (periodicity of `w` in `q`). -/
def CgiAprioriQ : Prop :=
  ∀ r : ℝ, 1 < r → ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∀ w : Coord → ℂ, CgiNice c r w →
    ∀ lam : ℝ, 0 < lam → cylNorm c r (cdv 1 w) ≤
      ENNReal.ofReal C * (ENNReal.ofReal lam⁻¹ * cylNorm c r w +
        ENNReal.ofReal lam * cylNorm c r (cdv 1 (cdv 1 w)))

/-- The a priori inequality for nice functions with constant `C` (A). -/
def AprioriAt (c r C : ℝ) : Prop :=
  ∀ w : Coord → ℂ, CgiNice c r w → ∀ (i : Fin 2) (lam : ℝ), 0 < lam →
    cylNorm c r (cdv i.succ w) ≤
      ENNReal.ofReal C * (ENNReal.ofReal lam⁻¹ * cylNorm c r w +
        ENNReal.ofReal lam * ∑ k : Fin 2, ∑ l : Fin 2, cylNorm c r (cdv k.succ (cdv l.succ w)))

/-- The hypotheses of `CylGradInterp` on `(u, D2)`. -/
def CgiData (c r : ℝ) (u : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ) : Prop :=
  QPeriodicS c u ∧ AEStronglyMeasurable u volume ∧ cylNorm c r u < ⊤ ∧
  (∀ i j, QPeriodicS c (D2 i j) ∧ AEStronglyMeasurable (D2 i j) volume ∧
      cylNorm c r (D2 i j) < ⊤) ∧
  (∀ (i j : Fin 2) (φ : Coord → ℝ), IsSTTestCoord φ →
      ∫ x, u x * (cpd i.succ (fun y => cpd j.succ φ y) x : ℂ) = ∫ x, D2 i j x * (φ x : ℂ))

/-- Smooth periodic approximants of `(u, D2)`: `w n → u` and `∂_k∂_l w n → D2 k l` in
`L^r(cylMeas c)`. -/
def CgiApprox (c r : ℝ) (u : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ)
    (w : ℕ → Coord → ℂ) : Prop :=
  (∀ n, CgiNice c r (w n)) ∧
  Tendsto (fun n => cylNorm c r (fun x => w n x - u x)) atTop (𝓝 0) ∧
  ∀ k l : Fin 2, Tendsto (fun n => cylNorm c r (fun x => cdv k.succ (cdv l.succ (w n)) x - D2 k l x))
    atTop (𝓝 0)

/-- **Leaf (B, mollification).** Convolving `u` with a smooth mollifier in `(s, q, η)` gives
smooth periodic approximants; the weak identity for `D2` shows that the mollified second
derivatives are the mollified `D2`, hence converge in `L^r(cylMeas c)` (translation invariance of
`cylMeas c` in `s` and `η` and of periodic functions in `q`; `∂_i` of the mollification is
`(∂_i ρ_ε) ⋆ u`, in `L^r` by Young). -/
def CgiMollify : Prop :=
  ∀ r : ℝ, 1 < r → ∀ c : ℝ, 0 < c → ∀ (u : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ),
    CgiData c r u D2 → ∃ w : ℕ → Coord → ℂ, CgiApprox c r u D2 w

/-- **Leaf (C, limit).** If the a priori inequality holds with constant `C` on nice functions
and nice `w n` approximate `(u, D2)`, then the first derivatives `∂_i w n` are Cauchy in
`L^r(cylMeas c)` (apply the inequality to `w n - w m`), their limit `D1 i` is periodic and
measurable, satisfies the weak identity (integrate by parts against `φ`; the pairing with a
compactly supported `φ` is controlled by finitely many cells and Hölder, using periodicity) and
inherits the inequality (norms converge). -/
def CgiLimit : Prop :=
  ∀ r : ℝ, 1 < r → ∀ c C : ℝ, 0 < c → 0 < C → AprioriAt c r C →
    ∀ (u : Coord → ℂ) (D2 : Fin 2 → Fin 2 → Coord → ℂ) (w : ℕ → Coord → ℂ),
    CgiApprox c r u D2 w → QPeriodicS c u → AEStronglyMeasurable u volume →
    (∀ k l : Fin 2, AEStronglyMeasurable (D2 k l) volume) →
    ∃ D1 : Fin 2 → Coord → ℂ,
      (∀ i, QPeriodicS c (D1 i) ∧ AEStronglyMeasurable (D1 i) volume) ∧
      (∀ (i : Fin 2) (φ : Coord → ℝ), IsSTTestCoord φ →
        ∫ x, u x * (cpd i.succ φ x : ℂ) = -∫ x, D1 i x * (φ x : ℂ)) ∧
      ∀ (i : Fin 2) (lam : ℝ), 0 < lam → cylNorm c r (D1 i) ≤ cgiRhs c r C lam u D2

/-- The two directional a priori leaves combine to `AprioriAt`. -/
theorem aprioriAt_of (hη : CgiAprioriEta) (hq : CgiAprioriQ) :
    ∀ r : ℝ, 1 < r → ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → AprioriAt c r C := by
  intro r hr
  obtain ⟨C1, hC1, h1⟩ := hη r hr
  obtain ⟨C2, hC2, h2⟩ := hq r hr
  refine ⟨C1 + C2, by positivity, fun c hc w hw i lam hlam => ?_⟩
  have hgen : ∀ k l : Fin 2, cylNorm c r (cdv k.succ (cdv l.succ w)) ≤
      ∑ k : Fin 2, ∑ l : Fin 2, cylNorm c r (cdv k.succ (cdv l.succ w)) := by
    intro k l
    refine le_trans ?_ (Finset.single_le_sum (f := fun k : Fin 2 =>
      ∑ l : Fin 2, cylNorm c r (cdv k.succ (cdv l.succ w))) (fun _ _ => bot_le) (Finset.mem_univ k))
    exact Finset.single_le_sum (f := fun l : Fin 2 => cylNorm c r (cdv k.succ (cdv l.succ w)))
      (fun _ _ => bot_le) (Finset.mem_univ l)
  have hsum : cylNorm c r (cdv 2 (cdv 2 w)) ≤
      ∑ k : Fin 2, ∑ l : Fin 2, cylNorm c r (cdv k.succ (cdv l.succ w)) := hgen 1 1
  have hsum' : cylNorm c r (cdv 1 (cdv 1 w)) ≤
      ∑ k : Fin 2, ∑ l : Fin 2, cylNorm c r (cdv k.succ (cdv l.succ w)) := hgen 0 0
  set S := ∑ k : Fin 2, ∑ l : Fin 2, cylNorm c r (cdv k.succ (cdv l.succ w))
  have key : ∀ C' : ℝ, 0 ≤ C' → C' ≤ C1 + C2 → ∀ X : ℝ≥0∞, X ≤ ENNReal.ofReal C' *
      (ENNReal.ofReal lam⁻¹ * cylNorm c r w + ENNReal.ofReal lam * S) → X ≤
      ENNReal.ofReal (C1 + C2) *
      (ENNReal.ofReal lam⁻¹ * cylNorm c r w + ENNReal.ofReal lam * S) := fun C' h0 hle X hX =>
    hX.trans (by gcongr)
  fin_cases i
  · refine key C2 hC2.le (by linarith) _ ((h2 c hc w hw lam hlam).trans ?_)
    gcongr
  · refine key C1 hC1.le (by linarith) _ ((h1 c hc w hw lam hlam).trans ?_)
    gcongr

/-- **Reduction.** `CylGradInterp` from the a priori inequality, mollification and the limit. -/
theorem cylGradInterp_of (hη : CgiAprioriEta) (hq : CgiAprioriQ) (hM : CgiMollify)
    (hL : CgiLimit) : CylGradInterp := by
  intro r hr
  obtain ⟨C, hC, hA⟩ := aprioriAt_of hη hq r hr
  refine ⟨C, hC, fun c hc u D2 hup hum hun hD hw => ?_⟩
  have hdata : CgiData c r u D2 := ⟨hup, hum, hun, hD, hw⟩
  obtain ⟨w, hwA⟩ := hM r hr c hc u D2 hdata
  exact hL r hr c C hc hC (hA c hc) u D2 w hwA hup hum (fun i j => (hD i j).2.1)

end UnforcedLeray.Short.IIb
