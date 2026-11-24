import UnforcedLeray.Short.PartIIIa.StressSpaces
import UnforcedLeray.Short.PartIIIa.FullClock
import UnforcedLeray.Short.PartIIIa.SeparatedKernels

/-!
# Part III-a: helper targets for the drafters


`theorem <lowerName> : <Name>` in a NEW file). They are pure real analysis or short assemblies of
the statement files. `scalingBounds_of_parts` is already proved.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal

namespace UnforcedLeray.Short.IIIa

/-- Cauchy-Schwarz in the age integral (SP 2753-2758): `∫_A^∞ s^{-5/4}h ≤ A^{-1/2}
(∫_A^∞ s^{-1/2}h²)^{1/2}`, from `∫_A^∞ s^{-2}ds = A⁻¹`. -/
def AgeCS : Prop :=
  ∀ A : ℝ, 0 < A → ∀ h : ℝ → ℝ≥0∞, Measurable h →
    ∫⁻ s in Ioi A, ENNReal.ofReal (s ^ (-5 / 4 : ℝ)) * h s ≤
      ENNReal.ofReal (A ^ (-1 / 2 : ℝ)) *
        (∫⁻ s in Ioi A, ENNReal.ofReal (s ^ (-1 / 2 : ℝ)) * h s ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-- Transverse Cauchy-Schwarz (SP 2747-2752): for `m_Z > 3/2` there is `C` with, for `s ≥ 1`,
`∫(1 + |η|/√s) g(η) dη ≤ C s^{1/4} (∫ W² g²)^{1/2}`, `W² = (1 + (η/√(1+s))²)^{m_Z}`
(uses `∫⟨x⟩^{2-2m_Z}dx < ∞`). -/
def TransverseCS : Prop :=
  ∀ mZ : ℝ, 3 / 2 < mZ → ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℝ, 1 ≤ s → ∀ g : ℝ → ℝ≥0∞, Measurable g →
    ∫⁻ η : ℝ, ENNReal.ofReal (1 + |η| / Real.sqrt s) * g η ≤
      ENNReal.ofReal (C * s ^ (1 / 4 : ℝ)) *
        (∫⁻ η : ℝ, ENNReal.ofReal ((1 + (η / Real.sqrt (1 + s)) ^ 2) ^ mZ) * g η ^ (2 : ℝ)) ^
          (1 / 2 : ℝ)

/-- `StressMoment` from the two Cauchy-Schwarz steps (SP 2747-2762). -/
def StressMomentOfParts : Prop := AgeCS → TransverseCS → StressMoment

/-- Polar coordinates and `u = |x'|^{-2}` (SP 2790-2795):
`∫_{ℝ²} f(|x'|^{-2}) dx' = π∫_0^∞ u^{-2}f(u) du`. -/
def PlaneRadialInv : Prop :=
  ∀ f : ℝ → ℝ≥0∞, Measurable f →
    ∫⁻ x' : ℝ × ℝ, f ((x'.1 ^ 2 + x'.2 ^ 2)⁻¹) =
      ENNReal.ofReal Real.pi * ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal (u ^ (-2 : ℝ)) * f u

/-- `OuterMomentIdentity` from `PlaneRadialInv` and the scaling `Y = η/√u` (SP 2790-2795). -/
def OuterMomentOfParts : Prop := PlaneRadialInv → OuterMomentIdentity

/-- The scaling integral behind `sep:kernel` (SP 3604-3606, "substitution `a = |x|²r`"):
for `s > 1`, `r > 0`, `∫_0^∞ a^{-s}e^{-r²/(8a)}da = r^{2-2s}∫_0^∞ ρ^{-s}e^{-1/(8ρ)}dρ < ∞`. -/
def GaussInvIntegral : Prop :=
  ∀ s r : ℝ, 1 < s → 0 < r →
    (∫⁻ a in Ioi (0 : ℝ), ENNReal.ofReal (a ^ (-s) * Real.exp (-r ^ 2 / (8 * a))) =
      ENNReal.ofReal (r ^ (2 - 2 * s)) *
        ∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (ρ ^ (-s) * Real.exp (-1 / (8 * ρ)))) ∧
    (∫⁻ ρ in Ioi (0 : ℝ), ENNReal.ofReal (ρ ^ (-s) * Real.exp (-1 / (8 * ρ)))) < ⊤

/-- Derivative bounds of the heat kernel (input of `sep:kernel`): for each `m` there is `C` with
`‖D^mG_a(x)‖ ≤ C a^{-(3+m)/2}e^{-|x|²/(8a)}` for all `a > 0`, `x`. -/
def HeatGBound : Prop :=
  ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a → ∀ x : Space,
    ‖iteratedFDeriv ℝ m (heatG a) x‖ ≤
      C * a ^ (-(3 + (m : ℝ)) / 2) * Real.exp (-‖x‖ ^ 2 / (8 * a))

/-- The Hardy-type inequality `eq:short-causal-hardy` (SP 3499-3503): for `σ > -3/4`,
`‖∫_0^s (t/s)^σ(s-t)^{-1/2}f(t)dt‖_{L²(s^{-3/2}ds)} ≤ B(σ+3/4, 1/2)‖f‖_{L²(s^{-1/2}dt)}`
(substitute `t = su`, Minkowski in `u`; `B(x,y) = ∫_0^1 u^{x-1}(1-u)^{y-1}du`). -/
def HardyKernel : Prop :=
  ∀ σ : ℝ, -(3 / 4) < σ → ∀ f : ℝ → ℝ≥0∞, Measurable f →
    (∫⁻ s in Ioi (0 : ℝ), ENNReal.ofReal (s ^ (-3 / 2 : ℝ)) *
        (∫⁻ t in Ioo (0 : ℝ) s,
          ENNReal.ofReal ((t / s) ^ σ * (s - t) ^ (-1 / 2 : ℝ)) * f t) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (∫ u in Ioo (0 : ℝ) 1, u ^ (σ + 3 / 4 - 1) * (1 - u) ^ (-1 / 2 : ℝ)) *
        (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (t ^ (-1 / 2 : ℝ)) * f t ^ (2 : ℝ)) ^ (1 / 2 : ℝ)

/-- Minkowski's integral inequality `‖T‖_{L²_τL¹_y} ≤ ‖T‖_{L¹_yL²_τ}` (SP 3670-3674). -/
def LtauMinkowski : Prop :=
  ∀ P : ℝ, 0 < P → ∀ T : ℝ → Space → Matrix (Fin 3) (Fin 3) ℝ,
    (∀ i j, Measurable fun p : ℝ × Space => T p.1 p.2 i j) →
      ltauLq P 1 (srcNorm T) ≤ ∫⁻ z : Space, ltauAt P (fun τ => srcNorm T τ z)

/-- `SepThinGlobal` from `SepYoung` (`p = 1`, `b = q`) and Minkowski (SP 3670-3680). -/
def ThinGlobalOfParts : Prop := SepYoung → LtauMinkowski → SepThinGlobal

/-! ## Scaling bounds, in three parts (SP 2982-2989) -/

/-- `‖J_a W‖_{X_{m,c}} ≤ a^{(m-3)/2}‖W‖_{X_{m,d}}`, `c = √a d` (change of variables `x = √a y`,
`⟨√a y⟩ ≤ √a⟨y⟩`). -/
def ScalingJa : Prop :=
  ∀ m : ℝ, 0 ≤ m → ∀ a d : ℝ, 1 ≤ a → 0 < d → ∀ W : ℝ × ℝ → ℂ, Measurable W →
    xNorm (d * Real.sqrt a) m (Jscale a W) ≤ ENNReal.ofReal (a ^ ((m - 3) / 2)) * xNorm d m W

/-- `‖J_a⁻¹ f‖_{X_{m,d}} ≤ a^{3/2}‖f‖_{X_{m,c}}` (`⟨x/√a⟩ ≤ ⟨x⟩`). -/
def ScalingJaInv : Prop :=
  ∀ m : ℝ, 0 ≤ m → ∀ a d : ℝ, 1 ≤ a → 0 < d → ∀ f : ℝ × ℝ → ℂ, Measurable f →
    xNorm d m (JscaleInv a f) ≤ ENNReal.ofReal (a ^ (3 / 2 : ℝ)) * xNorm (d * Real.sqrt a) m f

/-- `‖J_a⁻¹f‖_{(H^1_{-m,d})^*} ≤ a^{3/2}‖f‖_{(H^1_{-m,c})^*}`: `⟨J_a⁻¹f,φ⟩ = a⟨f,φ(·/√a)⟩` and
`‖φ(·/√a)‖_{H^1_{-m,c}} ≤ √a‖φ‖_{H^1_{-m,d}}`. -/
def ScalingJaInvDual : Prop :=
  ∀ m : ℝ, 0 ≤ m → ∀ a d : ℝ, 1 ≤ a → 0 < d → ∀ f : ℝ × ℝ → ℂ, Measurable f →
    negNorm d m (JscaleInv a f) ≤ ENNReal.ofReal (a ^ (3 / 2 : ℝ)) * negNorm (d * Real.sqrt a) m f

/-- `ScalingBounds` is the conjunction of the three parts. -/
theorem scalingBounds_of_parts (h1 : ScalingJa) (h2 : ScalingJaInv) (h3 : ScalingJaInvDual) :
    ScalingBounds :=
  fun m hm a d ha hd => ⟨h1 m hm a d ha hd, h2 m hm a d ha hd, h3 m hm a d ha hd⟩

end UnforcedLeray.Short.IIIa
