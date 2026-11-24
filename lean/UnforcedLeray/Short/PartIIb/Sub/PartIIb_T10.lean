import UnforcedLeray.Short.PartIIb.Bridge.Consequences
import UnforcedLeray.Short.PartIIb.Tasks.NvCNorm
import UnforcedLeray.Short.PartIIb.StatementsFree

/-!
# `PartII-b:T10` (`ProfileGraphPhys`): decomposition

Source of record: `the November 2 reference manuscript`, lines 1912-1938
(`bg:profile-graph`), through the Cartesian foundation `bg:common-body-graph` (1356-1420), already
available in the field model as `field_response_exists` / `field_graph_bound`
(`Bridge/Consequences.lean`, instantiated with `lerayPairSol`, `solSeparation`).

The remaining work is the dictionary between profiles `b ∈ H_r` and axisymmetric no-swirl fields
`N_v b ∈ Y_r` (`P = 2εc`, `R = ε⁻¹`), isolated in the seven Props below.  Each is a true source fact
(SP 1902-1921: `‖N_v b‖_{Y_r} = (πR²)^{1/r}‖b‖_{H_r}` (`phaseLpNorm_NvC`), `𝒯(√s b) = √s (S+1/2) b`,
`∂_ρ(√s b) = s Q_ε b`, `∂_z(√s b) = s ∂_η b`, the chart `(τ, y) ↦ (s, q, η)` and rotation
equivariance of the response).  The target is proved from them in `profileGraphPhys_of`.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411 UnforcedLeray.RieszLp
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.Short.PartIIa

/-- The region `s > 0` of the chart (support of all tests and of the weights of `H_r`). -/
abbrev posReg : Measure Coord := volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))

/-- **`T10/1`** (SP 1902-1906): the lift of a profile of `H_r` lies in `Y_r`: periodic in the phase
(`QPeriodic`), measurable (`Axi.measurable_Nv`, `ChartNullPullback`), finite norm (`phaseLpNorm_NvC`). -/
def NvCInYr : Prop :=
  ∀ (c ε r : ℝ) (F : CProf), 0 < c → 0 < ε → 0 < r → InHr c r F →
    IsInYr (2 * ε * c) r (NvC ε⁻¹ F)

/-- **`T10/2`** (SP 1902-1906, 1634-1637): if the lift of an arbitrary profile `b` (values on `s ≤ 0`
irrelevant) lies in `Y_r`, then `b` agrees on `s > 0` with a profile `b' ∈ H_r` (`c`-periodicity of `b`
in `q` is the `P`-periodicity of `N_v b` in the phase, `q = t/(2ε)` + chart; measurability from the
chart being a diffeomorphism off the axis) whose lift is the same field. -/
def ProfileRegularize : Prop :=
  ∀ (c ε r : ℝ) (b : CProf), 0 < c → 0 < ε → 0 < r → IsInYr (2 * ε * c) r (NvC ε⁻¹ b) →
    ∃ b' : CProf, (∀ᵐ x ∂posReg, b' x = b x) ∧ b' =ᵐ[hMeas c r] b ∧ InHr c r b' ∧
      NvC ε⁻¹ b' =ᵐ[volume] NvC ε⁻¹ b

/-- **`T10/3`** (SP 1912-1921): `HasWeakVec` only sees the values on `s > 0` almost everywhere
(tests are compactly supported in `s > 0`). -/
def WeakVecCongr : Prop :=
  ∀ (v : Coord → Fin 3 → ℝ) (d : Coord → ℝ) (b b' g : CProf),
    (∀ᵐ x ∂posReg, b' x = b x) → HasWeakVec v d b g → HasWeakVec v d b' g

/-- **`T10/4`** (SP 1339-1364): `IsFreeResponse` depends on `f, w` only up to a.e. equality
(`pairF` integrates; periodicity, measurability, norms are a.e. notions). -/
def FreeResponseCongr : Prop :=
  ∀ (ν : ℝ) (μ : ℂ) (r P : ℝ) (f f' w w' : ℝ × Space → CVec3), 0 < P →
    f =ᵐ[volume] f' → w =ᵐ[volume] w' → IsFreeResponse ν μ r P f w → IsFreeResponse ν μ r P f' w'

/-- **`T10/5`** (SP 1912-1938, 1356-1420, 1634-1672): the free response to the lift of `F ∈ H_r`
is the lift of a profile `b ∈ H_r` (rotation equivariance of `(μ + L)⁻¹𝔓` on `Y_r`: injectivity of
`μ + L` on `D_r` (`bg:common-body-graph`) gives `w = ρ_θ w` a.e. for every rotation about the axis,
and a no-swirl axisymmetric field is `N_v b`, `Axi.range_JvY2`, `Axi.range_Jv`; then `b ∈ H_r` by
`ProfileRegularize`/`phaseLpNorm_NvC`). -/
def ResponseProfile : Prop :=
  ∀ (c ε r ν : ℝ) (μ : ℂ) (F : CProf) (w : ℝ × Space → CVec3), 0 < c → 0 < ε → 0 < ν →
    2 * ε * c ≤ 1 → 1 < r → r < 3 → 0 < μ.re + (3 / r - 1) / 2 → InHr c r F →
    IsFreeResponse ν μ r (2 * ε * c) (NvC ε⁻¹ F) w →
    ∃ b : CProf, InHr c r b ∧ NvC ε⁻¹ b =ᵐ[volume] w

/-- **`T10/6`** (SP 1912-1915 `𝒯(√s b) = √s(S + 1/2)b`, converse of `hasPtwOp_driftT_NvC`): if the
phase drift of the lift of `b ∈ H_r` is a field `d ∈ Y_r`, then `d = N_v(Sb + b/2)` for the weak
`S`-derivative `Sb ∈ H_r` of `b` (`d` is axisymmetric no-swirl by uniqueness of distributional
derivatives and equivariance of `𝒯`; chart identity tested against lifts of coordinate tests), and
`(πR²)^{1/r}‖Sb‖ ≤ ‖d‖ + ‖N_v b‖` (`phaseLpNorm_NvC`, triangle inequality). -/
def DriftRecovery : Prop :=
  ∀ (c ε r : ℝ) (b₀ : CProf) (d₀ : ℝ × Space → CVec3),
    0 < c → 0 < ε → 1 < r → InHr c r b₀ → IsInYr (2 * ε * c) r d₀ →
    HasPtwOp (2 * ε * c) driftT (NvC ε⁻¹ b₀) d₀ →
    ∃ Sb : CProf, HasWeakVec vS dZero b₀ Sb ∧ InHr c r Sb ∧
      ENNReal.ofReal ((Real.pi * (ε⁻¹) ^ 2) ^ (1 / r)) * hNorm c r Sb ≤
        phaseLpNorm (2 * ε * c) r d₀ + phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ b₀)

/-- **`T10/7`** (SP 1912-1921 `∂_ρ(√s b) = s Q_ε b`, `∂_z(√s b) = s ∂_η b`): the spatial gradient
of the lift of `b ∈ H_r`, if in `Y_r`, is the lift of `(√s Q_ε b, √s ∂_η b, …)`: the profile-side
weak derivatives `Q_ε b`, `∂_η b` exist, with `(πR²)^{1/r}(‖√s Q_ε b‖ + ‖√s ∂_η b‖) ≤ K Σ_j‖g_j‖`,
`K = K_r` independent of `c, ε` (pointwise `|s Q_ε b| + |s ∂_η b| ≲ |∇ N_v b|` through the chart,
`Lib/AxisymmetricB/RingChart`; same chart argument as `DriftRecovery`). -/
def GradRecovery : Prop :=
  ∀ r : ℝ, 1 < r → r < 3 → ∃ K : ℝ, 0 < K ∧
    ∀ (c ε : ℝ) (b : CProf) (g : Fin 3 → ℝ × Space → CVec3), 0 < c → 0 < ε → InHr c r b →
      (∀ j, IsInYr (2 * ε * c) r (g j)) →
      (∀ j, HasPtwOp (2 * ε * c) (fun Φ => -(dy j Φ)) (NvC ε⁻¹ b) (g j)) →
      ∃ Qb Eb : CProf, HasWeakVec (vQ ε) (dQ ε) b Qb ∧ HasWeakVec vEta dZero b Eb ∧
        ENNReal.ofReal ((Real.pi * (ε⁻¹) ^ 2) ^ (1 / r)) *
            (hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb)) ≤
          ENNReal.ofReal K * ∑ j, phaseLpNorm (2 * ε * c) r (g j)

/-- **`ProfileGraphPhys`** from the field-model bridge and the seven profile/field dictionary Props
(SP 1912-1938).  `hLP`, `hSS` are `lerayPairSol`, `solSeparation`. -/
theorem profileGraphPhys_of (hLP : LerayPairSol) (hSS : SolSeparation) (h1 : NvCInYr)
    (h2 : ProfileRegularize) (h3 : WeakVecCongr) (h4 : FreeResponseCongr)
    (h5 : ResponseProfile) (h6 : DriftRecovery) (h7 : GradRecovery) : ProfileGraphPhys := by
  intro r hr1 hr3 μ hμ
  have hr0 : 0 < r := by linarith
  obtain ⟨C₁, hC₁0, hC₁⟩ := field_graph_bound hLP hSS hr1 hr3
  obtain ⟨K, hK, hKb⟩ := h7 r hr1 hr3
  set A : ℝ := 1 + (1 + ‖μ‖) / (μ.re + (3 / r - 1) / 2) with hA
  have hA0 : 0 ≤ A := by rw [hA]; positivity
  have hRK : 0 < max 2 K := lt_max_of_lt_left (by norm_num)
  refine ⟨max 2 K * C₁ * A + 1, add_pos_of_nonneg_of_pos
    (mul_nonneg (mul_nonneg hRK.le hC₁0) hA0) one_pos, ?_⟩
  intro ν c ε hν hc hε hε1 hP F hF
  have hP0 : 0 < 2 * ε * c := by positivity
  constructor
  · have hfY := h1 c ε r F hc hε hr0 hF
    obtain ⟨w, hw⟩ := field_response_exists hLP hfY hP0 hP hν hμ hr1 hr3
    obtain ⟨b, hb, hbw⟩ := h5 c ε r ν μ F w hc hε hν hP hr1 hr3 hμ hF hw
    exact ⟨b, hb, h4 ν μ r _ _ _ w _ hP0 Filter.EventuallyEq.rfl hbw.symm hw⟩
  · intro b hb
    have hbY : IsInYr (2 * ε * c) r (NvC ε⁻¹ b) := hb.mem_w
    obtain ⟨b', hbb'p, hbb'h, hb'H, hNN⟩ := h2 c ε r b hc hε hr0 hbY
    have hb'R : IsFreeResponse ν μ r (2 * ε * c) (NvC ε⁻¹ F) (NvC ε⁻¹ b') :=
      h4 ν μ r _ _ _ _ _ hP0 Filter.EventuallyEq.rfl hNN.symm hb
    have hfY := h1 c ε r F hc hε hr0 hF
    obtain ⟨a, haY, hap⟩ := hb'R.lapl
    obtain ⟨d, hdY, hdp⟩ := hb'R.drift
    obtain ⟨g, hgY, hgp, hbound⟩ := hC₁ (2 * ε * c) ν μ _ _ hP0 hP hν hμ hfY hb'R
    have hbd := hbound a d haY hap hdY hdp
    obtain ⟨Sb, hSb, -, hSbn⟩ := h6 c ε r b' d hc hε hr1 hb'H hdY hdp
    obtain ⟨Qb, Eb, hQ, hE, hQEn⟩ := hKb c ε b' g hc hε hb'H hgY hgp
    have hNb : phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ b') =
        ENNReal.ofReal ((Real.pi * (ε⁻¹) ^ 2) ^ (1 / r)) * hNorm c r b' :=
      phaseLpNorm_NvC hc hr0 hε b' hb'H.periodic hb'H.meas
    have hNF : phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ F) =
        ENNReal.ofReal ((Real.pi * (ε⁻¹) ^ 2) ^ (1 / r)) * hNorm c r F :=
      phaseLpNorm_NvC hc hr0 hε F hF.periodic hF.meas
    have hbb : hNorm c r b = hNorm c r b' := eLpNorm_congr_ae hbb'h.symm
    have hsym : ∀ᵐ x ∂posReg, b x = b' x := hbb'p.mono fun x hx => hx.symm
    refine ⟨Sb, Qb, Eb, h3 vS dZero b' b Sb hsym hSb, h3 _ _ b' b Qb hsym hQ,
      h3 _ _ b' b Eb hsym hE, ?_⟩
    rw [hbb]
    set κ : ℝ≥0∞ := ENNReal.ofReal ((Real.pi * (ε⁻¹) ^ 2) ^ (1 / r)) with hκ
    have hκ0 : κ ≠ 0 := by
      rw [hκ, Ne, ENNReal.ofReal_eq_zero, not_le]
      positivity
    have hκt : κ ≠ ⊤ := ENNReal.ofReal_ne_top
    have fw := hb'R.mem_w.finite
    have fd := hdY.finite
    have ff := hfY.finite
    have fg : ∀ j, phaseLpNorm (2 * ε * c) r (g j) ≠ ⊤ := fun j => (hgY j).finite.ne
    set Nw := phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ b') with hNw
    set Nd := phaseLpNorm (2 * ε * c) r d with hNd
    set Nf := phaseLpNorm (2 * ε * c) r (NvC ε⁻¹ F) with hNf
    set G := ∑ j, phaseLpNorm (2 * ε * c) r (g j) with hG
    have step1 : κ * (hNorm c r b' + hNorm c r Sb +
          ENNReal.ofReal (Real.sqrt ν) * (hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb))) ≤
        Nw + (Nd + Nw) + ENNReal.ofReal (Real.sqrt ν) * (ENNReal.ofReal K * G) := by
      rw [mul_add, mul_add, ← hNb, mul_left_comm]
      gcongr
    have hreal : Nw + (Nd + Nw) + ENNReal.ofReal (Real.sqrt ν) * (ENNReal.ofReal K * G) ≤
        ENNReal.ofReal (max 2 K * C₁ * A + 1) * Nf := by
      have hGr : G = ENNReal.ofReal (∑ j, (phaseLpNorm (2 * ε * c) r (g j)).toReal) := by
        rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => ENNReal.toReal_nonneg)]
        exact Finset.sum_congr rfl fun j _ => (ENNReal.ofReal_toReal (fg j)).symm
      have hNwr : Nw = ENNReal.ofReal Nw.toReal := (ENNReal.ofReal_toReal fw.ne).symm
      have hNdr : Nd = ENNReal.ofReal Nd.toReal := (ENNReal.ofReal_toReal fd.ne).symm
      have hNfr : Nf = ENNReal.ofReal Nf.toReal := (ENNReal.ofReal_toReal ff.ne).symm
      set gr : ℝ := ∑ j, (phaseLpNorm (2 * ε * c) r (g j)).toReal with hgr
      have hgr0 : 0 ≤ gr := Finset.sum_nonneg fun j _ => ENNReal.toReal_nonneg
      have ha0 : 0 ≤ (phaseLpNorm (2 * ε * c) r a).toReal := ENNReal.toReal_nonneg
      have hsq : 0 ≤ Real.sqrt ν := Real.sqrt_nonneg ν
      have hnw : 0 ≤ Nw.toReal := ENNReal.toReal_nonneg
      have hnd : 0 ≤ Nd.toReal := ENNReal.toReal_nonneg
      have hnf : 0 ≤ Nf.toReal := ENNReal.toReal_nonneg
      have hmax2 : 2 ≤ max 2 K := le_max_left _ _
      have hmaxK : K ≤ max 2 K := le_max_right _ _
      have hT : Nw.toReal + Nd.toReal + Real.sqrt ν * gr ≤ C₁ * A * Nf.toReal := by
        have := hbd
        rw [hA]
        linarith
      have key : Nw.toReal + (Nd.toReal + Nw.toReal) + Real.sqrt ν * (K * gr) ≤
          (max 2 K * C₁ * A + 1) * Nf.toReal := by
        have e1 : Nw.toReal + (Nd.toReal + Nw.toReal) + Real.sqrt ν * (K * gr) ≤
            max 2 K * (Nw.toReal + Nd.toReal + Real.sqrt ν * gr) := by
          have h1 : Real.sqrt ν * (K * gr) ≤ max 2 K * (Real.sqrt ν * gr) := by
            have : K * (Real.sqrt ν * gr) ≤ max 2 K * (Real.sqrt ν * gr) :=
              mul_le_mul_of_nonneg_right hmaxK (mul_nonneg hsq hgr0)
            nlinarith
          nlinarith [mul_le_mul_of_nonneg_right hmax2 hnw, mul_le_mul_of_nonneg_right
            (show (1:ℝ) ≤ max 2 K by linarith) hnd]
        have e2 := mul_le_mul_of_nonneg_left hT hRK.le
        nlinarith
      have e : Nw + (Nd + Nw) + ENNReal.ofReal (Real.sqrt ν) * (ENNReal.ofReal K * G) =
          ENNReal.ofReal (Nw.toReal + (Nd.toReal + Nw.toReal) + Real.sqrt ν * (K * gr)) := by
        rw [ENNReal.ofReal_add (add_nonneg hnw (add_nonneg hnd hnw))
          (mul_nonneg hsq (mul_nonneg hK.le hgr0)), ENNReal.ofReal_add hnw (add_nonneg hnd hnw),
          ENNReal.ofReal_add hnd hnw, ENNReal.ofReal_mul hsq, ENNReal.ofReal_mul hK.le,
          ← hNwr, ← hNdr, ← hGr]
      have hC0 : 0 ≤ max 2 K * C₁ * A + 1 :=
        add_nonneg (mul_nonneg (mul_nonneg hRK.le hC₁0) hA0) zero_le_one
      rw [e]
      calc _ ≤ ENNReal.ofReal ((max 2 K * C₁ * A + 1) * Nf.toReal) := ENNReal.ofReal_le_ofReal key
        _ = _ := by rw [ENNReal.ofReal_mul hC0, ← hNfr]
    have hfin : κ * (hNorm c r b' + hNorm c r Sb +
          ENNReal.ofReal (Real.sqrt ν) * (hNorm c r (sqrtS Qb) + hNorm c r (sqrtS Eb))) ≤
        κ * (ENNReal.ofReal (max 2 K * C₁ * A + 1) * hNorm c r F) := by
      refine step1.trans (hreal.trans (le_of_eq ?_))
      rw [hNF, mul_left_comm]
    exact (ENNReal.mul_le_mul_iff_right hκ0 hκt).1 hfin

end UnforcedLeray.Short.IIb
