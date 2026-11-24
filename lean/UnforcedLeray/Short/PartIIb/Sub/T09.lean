import UnforcedLeray.Short.PartIIb.Sub.T08

/-!
# Part II-b, task `PartII-b:T09`: divergence and Laplacian of the ring lift (conditional)

Source of record: `the November 2 reference manuscript`, lines 1639-1668
(`A_ε = -S + ν s[(Q_ε² + ∂_η²) I - ε² E]`, `div(√s b) = s[(∂_q - εK) b_r + ∂_η b_z]`,
`K = 2S + η∂_η`, `Q_ε = ∂_q - ε(K+1)`) and 1912-1916 (`∂_ρ(√s b) = s Q_ε b`,
`∂_z(√s b) = s ∂_η b`).

Two corrections to the task prose, forced by the cited lines (checked by hand with
`∂_ρ(√s F) = s Q_ε F`, `Q_ε(√s h) = √s (Q_ε - ε) h`):

* the Laplacian part of `A_ε` is `ν s[(Q_ε² + ∂_η²) b - ε² E b]` *without* the `-S b` term: `-S` is
  the drift part (`𝒯 - 1/2` lifts to `S`), so `νΔ(N_v b) = N_v(ν s[...])`;
* the hoop term acts on the radial component only: `Δ(f e_r) = (Δf - f/ρ²) e_r` and
  `Δ(g e_z) = (Δg) e_z`, so on the meridional pair `(b_r, b_z)` it is `E b = (b_r, 0)`
  (the source's `E = diag(1,1,0)` is in the frame `(r, φ, z)`).

Because the phase tests include the axis `ρ = 0` (`s = ∞`), the statements are made in the graph
class `r > 2`, `b, √s Q_ε b, √s ∂_η b ∈ H_r`: then `1/ρ ∈ L^{r'}_loc` and the axis is removable.

Targets proved here from leaves: `hasPtw_div_NvC_of`, `hasPtwOp_nuLap_NvC_of`.

Leaves:
* `DivSmooth`, `DivApprox`, `DivCont`, `DivVanish` (solenoidality).  `DivApprox` (density of nice
  profiles in the graph norm) is false for `r > 2` (the axis trace of the radial lift is continuous
  for the graph norm and vanishes on nice profiles); the divergence route is redesigned under
  `PartII-b:T09/2/1/1/org`.
* `LapSmooth`, `LapAwayAxis`, `LapAxisRemove` (Laplacian).  Density of nice profiles in the
  Laplacian graph (the former `LapApprox`) is false for `r > 2` for the same reason (the axis trace
  of `∇(N_v b)` is continuous on `W^{2,r}`).  Instead the identity is proved for phase tests
  vanishing near the axis (`LapAwayAxis`: fixed cutoff of `b` equal to `1` on the chart window of
  the test, approximation inside the window, `LapSmooth`), and the axis is removed by cutting off
  the test (`LapAxisRemove`, `Sub/PartIIb_T09_6b.lean`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
  UnforcedLeray.B0412

/-! ## Definitions -/

/-- A chart function pulled back to the cylinder: `x = (τ, y) ↦ g(s, q, η)(x)`, `R = ε⁻¹`
(`Axi.chart`, SP 1633-1637). -/
def sLift (R : ℝ) (g : Coord → ℂ) (x : ℝ × Space) : ℂ := g (Axi.chart R x.1 x.2)

/-- `s[(Q_ε + ε) b_r + ∂_η b_z]` (SP 1658-1660: `s[(∂_q - εK) b_r + ∂_η b_z]`, and
`∂_q - εK = Q_ε + ε`), given the weak derivatives `Qb = Q_ε b`, `Eb = ∂_η b`. -/
def gDiv (ε : ℝ) (b Qb Eb : CProf) : Coord → ℂ :=
  fun x => (x.1 : ℂ) * (Qb x 0 + (ε : ℂ) * b x 0 + Eb x 1)

/-- The graph class of `bg:profile-graph` without `S`: `b, √s Q_ε b, √s ∂_η b ∈ H_r`
(SP 1912-1918). -/
structure DivData (c r ε : ℝ) (b Qb Eb : CProf) : Prop where
  inHr : InHr c r b
  weakQ : HasWeakVec (vQ ε) (dQ ε) b Qb
  weakE : HasWeakVec vEta dZero b Eb
  inQ : InHr c r (sqrtS Qb)
  inE : InHr c r (sqrtS Eb)

/-- The hoop term `E b = (b_r, 0)` on a meridional vector (SP 1654). -/
def hoopE (v : CMerid) : CMerid := EuclideanSpace.single 0 (v 0)

/-- `ν s[(Q_ε² + ∂_η²) b - ε² E b]` (SP 1651-1653), given `Q2b = Q_ε(Q_ε b)`,
`E2b = ∂_η(∂_η b)`. -/
def lapProf (ν ε : ℝ) (b Q2b E2b : CProf) : CProf :=
  fun x => ((ν * x.1 : ℝ) : ℂ) • (Q2b x + E2b x - ((ε ^ 2 : ℝ) : ℂ) • hoopE (b x))

/-- The graph class for the Laplacian: first derivatives as in `DivData`, second derivatives weak
(`Q2b = Q_ε Q_ε b`, `E2b = ∂_η∂_η b`), and `ν s[...] ∈ H_r`, i.e. `νΔ(N_v b) ∈ Y_r`
(the exact Cartesian domain of `A_ε`, SP 1655). -/
structure LapData (c r ε ν : ℝ) (b Qb Eb Q2b E2b : CProf) : Prop where
  div : DivData c r ε b Qb Eb
  weakQ2 : HasWeakVec (vQ ε) (dQ ε) Qb Q2b
  weakE2 : HasWeakVec vEta dZero Eb E2b
  inLap : InHr c r (lapProf ν ε b Q2b E2b)

/-! ## Leaves: solenoidality -/

/-- **Leaf `T09/1`** (SP 1658-1660, 1912-1916): for nice `b`,
`⟪∇φ, N_v b⟫ = -⟪φ, s[(Q_ε+ε) b_r + ∂_η b_z]⟫` (the Cartesian divergence of the lift in the chart;
`⟪·,·⟫` the phase integral). -/
def DivSmooth : Prop :=
  ∀ (c ε : ℝ) (b Qb Eb : CProf), 0 < c → 0 < ε → NiceProf c b →
    HasWeakVec (vQ ε) (dQ ε) b Qb → HasWeakVec vEta dZero b Eb →
    ∀ φ : ℝ × Space → ℂ, IsPhaseTest (2 * ε * c) φ →
      pairF (2 * ε * c) (gradT φ) (NvC ε⁻¹ b) =
        -phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹ (gDiv ε b Qb Eb) x)

/-- **Leaf `T09/2`** (density; SP 1912-1918): nice profiles are dense in the graph class for
`‖b‖_{H_r} + ‖√s Q_ε b‖_{H_r} + ‖√s ∂_η b‖_{H_r}` (mollify in `log s`, `q`, `η`, cut off in `s`
and `η`; `Q_ε` and `∂_η` commute with the mollifiers up to bounded commutators). -/
def DivApprox : Prop :=
  ∀ (c ε r : ℝ) (b Qb Eb : CProf), 0 < c → 0 < ε → 2 < r → DivData c r ε b Qb Eb →
    ∃ bn Qbn Ebn : ℕ → CProf, (∀ n, NiceProf c (bn n) ∧ DivData c r ε (bn n) (Qbn n) (Ebn n)) ∧
      Tendsto (fun n => hNorm c r (fun x => bn n x - b x)) atTop (𝓝 0) ∧
      Tendsto (fun n => hNorm c r (sqrtS fun x => Qbn n x - Qb x)) atTop (𝓝 0) ∧
      Tendsto (fun n => hNorm c r (sqrtS fun x => Ebn n x - Eb x)) atTop (𝓝 0)

/-- **Leaf `T09/3`** (SP 1912-1918): for a phase test `φ` and `r > 2` the functional
`(b, Qb, Eb) ↦ ⟪φ, s[(Q_ε+ε) b_r + ∂_η b_z]⟫` is continuous for the graph norm.  Proof:
`|s Q b| = |N_v(√s Q b)|`, `|s b| = |N_v b|/ρ·R`, Hölder against `φ ∈ L^{r'}`, `φ/ρ ∈ L^{r'}`
(`r' < 2`), and `‖N_v b‖_{Y_r} = (πR²)^{1/r}‖b‖_{H_r}` (`phaseLpNorm_NvC`, `T07`). -/
def DivCont : Prop :=
  ∀ (c ε r : ℝ) (φ : ℝ × Space → ℂ) (b Qb Eb : CProf) (bn Qbn Ebn : ℕ → CProf),
    0 < c → 0 < ε → 2 < r → IsPhaseTest (2 * ε * c) φ → DivData c r ε b Qb Eb →
    (∀ n, DivData c r ε (bn n) (Qbn n) (Ebn n)) →
    Tendsto (fun n => hNorm c r (fun x => bn n x - b x)) atTop (𝓝 0) →
    Tendsto (fun n => hNorm c r (sqrtS fun x => Qbn n x - Qb x)) atTop (𝓝 0) →
    Tendsto (fun n => hNorm c r (sqrtS fun x => Ebn n x - Eb x)) atTop (𝓝 0) →
    Tendsto (fun n => phaseInt (2 * ε * c)
        (fun x => φ x * sLift ε⁻¹ (gDiv ε (bn n) (Qbn n) (Ebn n)) x)) atTop
      (𝓝 (phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹ (gDiv ε b Qb Eb) x)))

/-- **Leaf `T09/4`** (fundamental lemma; the chart `(τ, y) ↦ (s, q, η)` is a local
diffeomorphism off the axis, `ChartNull`): for data in the graph class, `⟪φ, sLift g⟫ = 0` for
every phase test iff `g = 0` a.e. on `s > 0`; here `g = s·h`, `h = Qb_r + ε b_r + Eb_z`. -/
def DivVanish : Prop :=
  ∀ (c ε r : ℝ) (b Qb Eb : CProf), 0 < c → 0 < ε → 2 < r → DivData c r ε b Qb Eb →
    ((∀ φ : ℝ × Space → ℂ, IsPhaseTest (2 * ε * c) φ →
      phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹ (gDiv ε b Qb Eb) x) = 0) ↔
    ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))),
      Qb x 0 + (ε : ℂ) * b x 0 + Eb x 1 = 0)

/-- The divergence formula for the whole graph class, from the three analytic leaves. -/
theorem divFormula_of (h1 : DivSmooth) (h2 : DivApprox) (h3 : DivCont) (h4 : DriftPairCont)
    {c ε r : ℝ} (hc : 0 < c) (hε : 0 < ε) (hr : 2 < r) {b Qb Eb : CProf}
    (hd : DivData c r ε b Qb Eb) (φ : ℝ × Space → ℂ) (hφ : IsPhaseTest (2 * ε * c) φ) :
    pairF (2 * ε * c) (gradT φ) (NvC ε⁻¹ b) =
      -phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹ (gDiv ε b Qb Eb) x) := by
  obtain ⟨bn, Qbn, Ebn, hn, t1, t2, t3⟩ := h2 c ε r b Qb Eb hc hε hr hd
  have e : ∀ n, pairF (2 * ε * c) (gradT φ) (NvC ε⁻¹ (bn n)) =
      -phaseInt (2 * ε * c) (fun x => φ x * sLift ε⁻¹ (gDiv ε (bn n) (Qbn n) (Ebn n)) x) :=
    fun n => h1 c ε (bn n) (Qbn n) (Ebn n) hc hε (hn n).1 (hn n).2.weakQ (hn n).2.weakE φ hφ
  have l1 := h4 c r ε (gradT φ) hc hε (by linarith) hφ.gradT b bn hd.inHr
    (fun n => (hn n).2.inHr) t1
  have l2 := (h3 c ε r φ b Qb Eb bn Qbn Ebn hc hε hr hφ hd (fun n => (hn n).2) t1 t2 t3).neg
  simp only [e] at l1
  exact tendsto_nhds_unique l1 l2

/-- **Target** `hasPtw_div_NvC`: the lift `N_v b` is solenoidal for phase tests iff the chart
identity `s[(∂_q - εK) b_r + ∂_η b_z] = 0` holds weakly (`∂_q - εK = Q_ε + ε`). -/
theorem hasPtw_div_NvC_of (h1 : DivSmooth) (h2 : DivApprox) (h3 : DivCont) (h4 : DriftPairCont)
    (h5 : DivVanish) {c ε r : ℝ} (hc : 0 < c) (hε : 0 < ε) (hr : 2 < r) {b Qb Eb : CProf}
    (hd : DivData c r ε b Qb Eb) :
    (∀ φ : ℝ × Space → ℂ, IsPhaseTest (2 * ε * c) φ →
        pairF (2 * ε * c) (gradT φ) (NvC ε⁻¹ b) = 0) ↔
      ∀ᵐ x ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set (ℝ × ℝ)))),
        Qb x 0 + (ε : ℂ) * b x 0 + Eb x 1 = 0 := by
  rw [← h5 c ε r b Qb Eb hc hε hr hd]
  refine forall_congr' fun φ => forall_congr' fun hφ => ?_
  rw [divFormula_of h1 h2 h3 h4 hc hε hr hd φ hφ, neg_eq_zero]

/-! ## Leaves: the Laplacian -/

/-- **Leaf `T09/5`** (SP 1651-1653, 1912-1916): the Cartesian Laplacian of the lift of a nice
profile: `νΔ(N_v b) = N_v(ν s[(Q_ε² + ∂_η²) b - ε² E b])` (`vecLap_liftMer`, `RingChart.lean`;
`Δ(f e_r) = (Δf - f/ρ²) e_r`, `Δ(g e_z) = Δg e_z`, `Δ(√s F) = √s s (Q_ε² + ∂_η²)F`). -/
def LapSmooth : Prop :=
  ∀ (c ε ν : ℝ) (b Qb Eb Q2b E2b : CProf), 0 < c → 0 < ε → NiceProf c b →
    HasWeakVec (vQ ε) (dQ ε) b Qb → HasWeakVec vEta dZero b Eb →
    HasWeakVec (vQ ε) (dQ ε) Qb Q2b → HasWeakVec vEta dZero Eb E2b →
    HasPtwOp (2 * ε * c) (nuLapT ν) (NvC ε⁻¹ b) (NvC ε⁻¹ (lapProf ν ε b Q2b E2b))

/-- A phase test vanishing in the tube `ϱ < δ` around the axis (`δ > 0`).  With its bounded
support, its chart image lies in a compact window `s ∈ [R²/Rad², R²/δ²]`, `|η| ≤ Rad √s`. -/
def OffAxisTest (P δ : ℝ) (Φ : ℝ × Space → CVec3) : Prop :=
  IsPhaseTest P Φ ∧ 0 < δ ∧ ∀ (τ : ℝ) (y : Space), Axi.ϱ y < δ → Φ (τ, y) = 0

/-- **Leaf `T09/6a`** (SP 1655-1668, 1902-1921): the Laplacian identity
`⟪νΔΦ, N_v b⟫ = ⟪Φ, N_v(ν s[(Q_ε² + ∂_η²) b - ε² E b])⟫` for phase tests vanishing near the
axis, for all `b` in the graph class.  Proof (`Sub/PartIIb_T09_6a.lean`): multiply the data by the
fixed cutoff `sBump k (s)`, equal to `1` on a neighbourhood of the chart window of `Φ`
(`LapCutWeak`, `LapCutInHr`, `LapCutSupport`); approximate the window data by nice profiles
(`LapEtaCutApprox`, `LapMollApprox`), apply `LapSmooth` and pass to the limit (`DriftPairCont`);
the cut data agree with the data where `Φ` lives. -/
def LapAwayAxis : Prop :=
  ∀ (c ε r ν : ℝ) (b Qb Eb Q2b E2b : CProf), 0 < c → 0 < ε → 2 < r →
    LapData c r ε ν b Qb Eb Q2b E2b → ∀ (δ : ℝ) (Φ : ℝ × Space → CVec3),
      OffAxisTest (2 * ε * c) δ Φ →
      pairF (2 * ε * c) (nuLapT ν Φ) (NvC ε⁻¹ b) =
        pairF (2 * ε * c) Φ (NvC ε⁻¹ (lapProf ν ε b Q2b E2b))

/-- **Leaf `T09/6b`** (SP 1667-1668: the domains are the exact Cartesian domains, no boundary is
introduced at either age end; SP 1919-1921: `∂_ρ(√s b) = s Q_ε b`): the axis `ϱ = 0` (`s = ∞`)
is removable for the Laplacian identity.  Cut the *test* off, `Φₙ = aₙ Φ`,
`aₙ = σ((n+1)²ϱ² - 1)`: `Δ(aₙΦ) = aₙΔΦ + wₙ E_hΦ + T_h(wₙΦ)` with `E_h = y₀∂₀ + y₁∂₁ = ϱ∂_ϱ`,
`∂_j aₙ = wₙ y_j`, and `⟪T_h F, N_v b⟫ = -⟪ϱF, N_v(√s Q_ε b)⟫` moves the last derivative onto `b`.
The remaining terms are bounded by `C(n+1)` on the tube `ϱ ≤ √2/(n+1)` of volume `O((n+1)⁻²)`,
hence are `O((n+1)^{2/r-1}) → 0` by Hölder, `r > 2`, using only `N_v b, ∂_ϱ N_v b ∈ L^r`.
The age end `s → 0` (`ϱ → ∞`) needs no cutoff since phase tests have bounded support.
Proof: `Sub/PartIIb_T09_6b.lean`. -/
def LapAxisRemove : Prop :=
  ∀ (c ε r ν : ℝ) (b Qb Eb Q2b E2b : CProf), 0 < c → 0 < ε → 2 < r →
    LapData c r ε ν b Qb Eb Q2b E2b →
    (∀ (δ : ℝ) (Φ : ℝ × Space → CVec3), OffAxisTest (2 * ε * c) δ Φ →
      pairF (2 * ε * c) (nuLapT ν Φ) (NvC ε⁻¹ b) =
        pairF (2 * ε * c) Φ (NvC ε⁻¹ (lapProf ν ε b Q2b E2b))) →
    HasPtwOp (2 * ε * c) (nuLapT ν) (NvC ε⁻¹ b) (NvC ε⁻¹ (lapProf ν ε b Q2b E2b))

/-- **Target** `hasPtwOp_nuLap_NvC`: `νΔ(N_v b) = N_v(ν s[(Q_ε² + ∂_η²) b - ε² E b])` in
distributions on `ℝ/Pℤ × ℝ³`, for `b` in the graph class. -/
theorem hasPtwOp_nuLap_NvC_of (h1 : LapAwayAxis) (h2 : LapAxisRemove)
    {c ε r ν : ℝ} (hc : 0 < c) (hε : 0 < ε) (hr : 2 < r) {b Qb Eb Q2b E2b : CProf}
    (hd : LapData c r ε ν b Qb Eb Q2b E2b) :
    HasPtwOp (2 * ε * c) (nuLapT ν) (NvC ε⁻¹ b) (NvC ε⁻¹ (lapProf ν ε b Q2b E2b)) :=
  h2 c ε r ν b Qb Eb Q2b E2b hc hε hr hd (h1 c ε r ν b Qb Eb Q2b E2b hc hε hr hd)

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.hasPtw_div_NvC_of
#print axioms UnforcedLeray.Short.IIb.hasPtwOp_nuLap_NvC_of
