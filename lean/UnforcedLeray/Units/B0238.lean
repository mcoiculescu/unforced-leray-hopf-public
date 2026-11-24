import UnforcedLeray.Units.B0238.Circulation
import UnforcedLeray.Units.B0238.Moments
import UnforcedLeray.Units.B0238.VorticityEq

/-!
# B0238 — The actual Gaussian cylinder train `(V_c, E_c)` (`unlabeled:4127`)

Blueprint unit **B0238** (`unlabeled:4127`, kind construction), `paper/main.tex` lines 4125–4134
(§`sec:st18-4795`, in §`sec:mixed-background`); depends on **B0140** (`eq:st18-t00140`, the train
initial-value problem) and refers to §`sec:train`; infrastructure INF13, INF16, INF24.

**Statement (tex 4125–4134).** Let `C_c = (ℝ/cℤ) × ℝ`, with `q ∈ [-c/2, c/2)`. Periodize the
initial Gaussian streamfunction, and let `(V_c, E_c)` be its exact two-dimensional Navier–Stokes
evolution at viscosity `ν`. The train is the one constructed in Section `sec:train`; its
Gaussian data have the finite weighted moments used below. It has zero circulation, odd velocity,
and even vorticity under `(q, η) ↦ (-q, -η)`.

**Formalization.**
* *Cylinder.* Decision D1 (`scoping/README.md` §3): fields on `C_c` are `c`-periodic functions on
  `Plane = ℝ × ℝ`, integrated over the centred cell `Cyl.cell c = [-c/2, c/2) × ℝ` with Lebesgue
  measure (`cell_eq`).
* *Data.* The periodized Gaussian stream is `B0140.trainStream c = P_c ψ₀`,
  `ψ(0) = -2∑ₙ e^{-|z-(nc,0)|²/4}` (tex 2050), and the velocity datum is
  `B0140.trainDatum c = ∇^⊥ψ(0) = P_c v₀` (unit B0140, reused, not redefined).
* *The evolution.* The train of §`sec:train` is a `B0140.TrainSol ν c` (INF16 T15 `TrainData`): a
  global smooth finite-energy `c`-periodic solution `(v, p)` of the 2D Navier–Stokes system with
  `v(0) = P_c v₀`, decaying stream `ψ` and central oddness (`B0140.IsTrain`). Its existence
  (Gallay–Slijepčević 2015, tex 2152–2161, INF16) is the named hypothesis
  `B0140.TrainIVPSolvable ν c`, which supplies the chosen train `B0140.train h`. For a train `tr`,
  `V_c = Vc tr = tr.v` and `E_c = Ec tr = curl V_c` (the vorticity of the evolution). The pair is
  the evolution in velocity and vorticity form: `V_c` solves the momentum equation (`isTrain_Vc`)
  and `E_c` solves the vorticity equation `∂_sE_c + V_c·∇E_c - νΔE_c = 0` for `s > 0`
  (`Ec_vorticity_equation`, proved from the momentum equation by taking the curl).
  *Notation clash:* here `V_c` is the actual train; the periodized heat vortex called `V_c` in
  §`sec:train` (tex 2196–2234, `Train.Vc`) is `V_c^p` of tex 4136.
* *Moments.* "The finite weighted moments used below" are those of the cell spaces
  `X_c = L²(C_c, (1+q²+η²)^m)` and `H^k_m` (tex 4149–4184): for every `c > 0`, derivative order
  `j`, real `m` and `p ≥ 1`, `∫_cell (1+q²+η²)^m ‖D^j V_c(0)‖^p < ∞` and
  `∫_cell (1+q²+η²)^m |E_c(0)|^p < ∞`, stated as integrability (no junk value of `∫`).
* *Symmetry.* `V_c(s, -z) = -V_c(s, z)` (field `odd` of the train, tex 2188) and
  `E_c(s, -z) = E_c(s, z)` (proved: `curl_neg_of_odd`), at every age `s ≥ 0`.
* *Zero circulation.* `∫_cell E_c(s) = 0`, stated with integrability. At `s = 0` it is proved
  outright (Gaussian bound and `Train.integral_cell_curl_datum`). At `s > 0` the vanishing is
  proved (`integral_cell_curl_eq_zero`: periodicity, `v = ∇^⊥ψ`, the decay of `ψ`) from the
  integrability of `E_c(s)` over one cell, which is the named hypothesis `VorticityIntegrable`
  (the `L¹` bound of the vorticity, tex 2181–2183, INF16 O2; not yet built).

**Hypotheses on `c`.** The manuscript has `c = ν^{-ρ}` with `0 < ν ≤ 1` (tex 2043–2044), so
`c ≥ 1`. Moments and zero circulation use only `c > 0`; the identification of the initial stream
`ψ(0)` (B0140 `IsTrain.stream_zero`) uses `c ≥ 1`.

**Uniqueness.** Uniqueness of the train (Gallay–Slijepčević, B0141) is not used: every
statement holds for every train `tr : TrainSol ν c`.

**Main declarations.** `cell_eq`, `Vc`, `Ec`, `VorticityIntegrable`, `contDiff_Vc`,
`isTrain_Vc`, `Ec_vorticity_equation`, `Vc_zero`, `Vc_zero_apply`, `stream_zero`, `Ec_zero`,
`Vc_odd`, `Ec_even`,
`moments_Vc_zero`, `moments_Ec_zero`, `integrableOn_Ec_zero`, `zero_circulation_zero`,
`integrableOn_Ec`, `zero_circulation`; whole unit `unit_B0238`. Helpers: `B0238/Partials.lean`,
`B0238/Circulation.lean`, `B0238/Moments.lean`, `B0238/SpaceTime.lean`, `B0238/VorticityEq.lean`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory
open scoped Topology ContDiff

namespace UnforcedLeray.B0238

open UnforcedLeray.Cyl (Plane)
open UnforcedLeray.Train (Vec toVec)
open UnforcedLeray.GaussianVortex (velocity vorticity)
open UnforcedLeray.B0140 (TrainSol TrainIVPSolvable IsTrain trainDatum trainStream)

/-! ### 1. The cylinder and the periodized Gaussian stream -/

/-- `C_c = (ℝ/cℤ) × ℝ` with `q ∈ [-c/2, c/2)` (tex 4127–4128): the centred cell. -/
theorem cell_eq (c : ℝ) : Cyl.cell c = Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ) := rfl

/-! ### 2. The pair `(V_c, E_c)` -/

/-- `V_c`: the velocity of the actual train `tr` (tex 4129–4130). -/
def Vc {ν c : ℝ} (tr : TrainSol ν c) : ℝ → Plane → Vec := tr.v

/-- `E_c = curl V_c = ∂_q V₂ - ∂_η V₁`: the vorticity of the evolution (tex 4129–4130). -/
def Ec {ν c : ℝ} (tr : TrainSol ν c) (s : ℝ) (z : Plane) : ℝ := Cyl.curl (tr.v s) z

/-- **Named hypothesis (not built): the train vorticity is in `L¹` of one cell at every positive
age.** Tex 2156 and 2181–2183: the datum vorticity is in `L¹ ∩ L^∞` with zero integral, and
"the conservative vorticity equation preserves its integral and its `L¹` and `L^∞` bounds"
(INF16 O2, scoping note `INF16-Cylinder2DNS.md` §2.1; unit B0142). Only integrability at
`s > 0` is assumed (at `s = 0` it is proved, `integrableOn_Ec_zero`); the vanishing of the
integral is then proved (`zero_circulation`). -/
def VorticityIntegrable {ν c : ℝ} (tr : TrainSol ν c) : Prop :=
  ∀ s : ℝ, 0 < s → IntegrableOn (Ec tr s) (Cyl.cell c)

/-- The train is an exact 2D Navier–Stokes evolution of the Gaussian datum on `C_c`
(tex 4129–4130, `B0140.IsTrain`): smooth, periodic, divergence free, the momentum equation for
`s > 0`, `V_c(0) = P_c v₀`, finite cell energy, decaying pressure and stream, centrally odd. -/
theorem isTrain_Vc {ν c : ℝ} (tr : TrainSol ν c) : IsTrain ν c (Vc tr) tr.p tr.ψ := tr.isTrain

/-- `V_c(s)` is `C^∞` in space at every age `s ≥ 0` (slice of the one-sided smoothness). -/
theorem contDiff_Vc {ν c : ℝ} (tr : TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) :
    ContDiff ℝ ∞ (Vc tr s) := by
  have h := tr.isTrain.smooth_v.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (s := univ) (fun z _ => ⟨mem_Ici.2 hs, mem_univ z⟩)
  exact contDiffOn_univ.1 h

/-- **The vorticity form of the evolution**: `E_c` solves
`∂_sE_c + V_c·∇E_c - νΔE_c = 0` for `s > 0` (classical partials; tex 2181, O1 of INF16), derived
from the momentum equation, `div V_c = 0` and the smoothness of the train
(`vorticityResidual_eq_zero`). -/
theorem Ec_vorticity_equation {ν c : ℝ} (tr : TrainSol ν c) {s : ℝ} (hs : 0 < s) (z : Plane) :
    deriv (fun t => Ec tr t z) s +
      (Vc tr s z 0 * Cyl.partialQ (Ec tr s) z + Vc tr s z 1 * Cyl.partialEta (Ec tr s) z) -
      ν * Train.lapS (Ec tr s) z = 0 :=
  vorticityResidual_eq_zero tr.isTrain.smooth_v tr.isTrain.smooth_p
    (fun s hs => tr.isTrain.solenoidal s hs.le) tr.isTrain.momentum hs z

/-- `V_c(0) = P_c v₀` (tex 2146). -/
theorem Vc_zero {ν c : ℝ} (tr : TrainSol ν c) : Vc tr 0 = trainDatum c := tr.isTrain.initial

/-- `V_c(q, η, 0) = ∑ₙ v₀(q - nc, η)` (tex 2146), the literal lattice sum. -/
theorem Vc_zero_apply {ν c : ℝ} (tr : TrainSol ν c) (z : Plane) :
    Vc tr 0 z = toVec (∑' n : ℤ, velocity (z.1 - n * c, z.2)) := by
  rw [Vc_zero]; rfl

/-- The initial stream is the periodized Gaussian stream,
`ψ(0)(q,η) = -2∑ₙ e^{-((q-nc)²+η²)/4}` (tex 2050, 4128), for `c ≥ 1`. -/
theorem stream_zero {ν c : ℝ} (tr : TrainSol ν c) (hc : 1 ≤ c) (q η : ℝ) :
    tr.ψ 0 (q, η) = -2 * ∑' n : ℤ, Real.exp (-((q - n * c) ^ 2 + η ^ 2) / 4) := by
  rw [tr.isTrain.stream_zero hc, B0140.trainStream_apply]

/-- `E_c(0) = P_c ω₀`, the periodized Gaussian vorticity `ω₀ = (2 - |x|²/2)e^{-|x|²/4}`. -/
theorem Ec_zero {ν c : ℝ} (tr : TrainSol ν c) (hc : c ≠ 0) (z : Plane) :
    Ec tr 0 z = Gaussian.periodize c vorticity z := by
  rw [Ec, tr.isTrain.initial]; exact B0140.curl_trainDatum hc z

/-! ### 3. Symmetry: odd velocity, even vorticity (tex 4131–4133) -/

/-- **Odd velocity**: `V_c(s, -q, -η) = -V_c(s, q, η)` at every age (tex 2188, 4132). -/
theorem Vc_odd {ν c : ℝ} (tr : TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) (z : Plane) :
    Vc tr s (-z) = -Vc tr s z :=
  tr.isTrain.odd s hs z

/-- **Even vorticity**: `E_c(s, -q, -η) = E_c(s, q, η)` at every age (tex 2191, 4132–4133). -/
theorem Ec_even {ν c : ℝ} (tr : TrainSol ν c) {s : ℝ} (hs : 0 ≤ s) (z : Plane) :
    Ec tr s (-z) = Ec tr s z :=
  curl_neg_of_odd (tr.isTrain.odd s hs) z

/-! ### 4. Finite weighted moments of the Gaussian data (tex 4130–4131) -/

/-- Every derivative of the initial velocity has finite weighted moments on the cell:
`∫_cell (1+q²+η²)^m ‖D^j V_c(0)‖^p < ∞` for `c > 0`, every `j`, real `m`, `p ≥ 1`. -/
theorem moments_Vc_zero {ν c : ℝ} (tr : TrainSol ν c) (hc : 0 < c) (j : ℕ) (m : ℝ) {p : ℕ}
    (hp : 1 ≤ p) :
    IntegrableOn (fun z => Cyl.ρc z ^ m * ‖iteratedFDeriv ℝ j (Vc tr 0) z‖ ^ p) (Cyl.cell c) := by
  rw [Vc_zero]; exact integrableOn_weight_jet_trainDatum hc j m hp

/-- The initial vorticity has finite weighted moments on the cell:
`∫_cell (1+q²+η²)^m |E_c(0)|^p < ∞` for `c > 0`, real `m`, `p ≥ 1` (the space `X_c`,
tex 4171–4184, at `p = 2`). -/
theorem moments_Ec_zero {ν c : ℝ} (tr : TrainSol ν c) (hc : 0 < c) (m : ℝ) {p : ℕ}
    (hp : 1 ≤ p) :
    IntegrableOn (fun z => Cyl.ρc z ^ m * |Ec tr 0 z| ^ p) (Cyl.cell c) := by
  simp only [Ec, tr.isTrain.initial]
  exact integrableOn_weight_curl_trainDatum hc m hp

/-! ### 5. Zero circulation (tex 4131–4132) -/

/-- The initial vorticity is integrable over one cell. -/
theorem integrableOn_Ec_zero {ν c : ℝ} (tr : TrainSol ν c) (hc : 0 < c) :
    IntegrableOn (Ec tr 0) (Cyl.cell c) := by
  have h : Ec tr 0 = Cyl.curl (trainDatum c) := by
    funext z; simp only [Ec, tr.isTrain.initial]
  rw [h]; exact integrableOn_curl_trainDatum hc

/-- **Zero circulation of the data**: `∫_cell E_c(0) = 0` (tex 2156), for every `c > 0`. -/
theorem zero_circulation_zero {ν c : ℝ} (tr : TrainSol ν c) (hc : 0 < c) :
    ∫ z in Cyl.cell c, Ec tr 0 z = 0 := by
  simp only [Ec, tr.isTrain.initial, B0169.trainDatum_eq_datum]
  exact Train.integral_cell_curl_datum hc

/-- The vorticity is integrable over one cell at every age, given `VorticityIntegrable` at
positive ages. -/
theorem integrableOn_Ec {ν c : ℝ} (tr : TrainSol ν c) (hc : 0 < c)
    (hL1 : VorticityIntegrable tr) {s : ℝ} (hs : 0 ≤ s) :
    IntegrableOn (Ec tr s) (Cyl.cell c) := by
  rcases hs.lt_or_eq with hs | hs
  · exact hL1 s hs
  · rw [← hs]; exact integrableOn_Ec_zero tr hc

/-- **Zero circulation at every age** (tex 4131–4132): `∫_cell E_c(s) = 0` for all `s ≥ 0`,
given the `L¹` hypothesis `VorticityIntegrable` (at `s = 0` it is `zero_circulation_zero`).
The vanishing is proved from periodicity, `V_c = ∇^⊥ψ` and the decay of `ψ`
(`integral_cell_curl_eq_zero`). -/
theorem zero_circulation {ν c : ℝ} (tr : TrainSol ν c) (hc : 0 < c)
    (hL1 : VorticityIntegrable tr) {s : ℝ} (hs : 0 ≤ s) :
    ∫ z in Cyl.cell c, Ec tr s z = 0 :=
  integral_cell_curl_eq_zero hc ((contDiff_Vc tr hs).of_le (by exact_mod_cast le_top))
    (tr.isTrain.periodic_v s hs) (tr.isTrain.stream_differentiable s hs) (tr.isTrain.stream s hs)
    (tr.isTrain.stream_decay s hs) (integrableOn_Ec tr hc hL1 hs)

/-! ### 6. The whole unit -/

/-- **Unit B0238** (tex 4125–4134). The centred cell of `C_c`; the periodized Gaussian stream;
the finite weighted moments of the Gaussian data; and, for every train `tr` of §`sec:train`
(`B0140.TrainSol ν c`, which exists under the named hypothesis `B0140.TrainIVPSolvable ν c`, see
`B0140.train`), the pair `(V_c, E_c) = (tr.v, curl tr.v)`: the exact 2D Navier–Stokes evolution
of the periodized datum in velocity and vorticity form, with `ψ(0)` the periodized Gaussian stream, finite weighted moments of
its data, odd velocity, even vorticity, zero circulation at `s = 0`, and zero circulation at
every age under the `L¹` hypothesis `VorticityIntegrable`. -/
theorem unit_B0238 :
    -- `C_c = (ℝ/cℤ) × ℝ` with `q ∈ [-c/2, c/2)`
    (∀ c : ℝ, Cyl.cell c = Ico (-c / 2) (c / 2) ×ˢ (univ : Set ℝ)) ∧
    -- the periodized initial Gaussian streamfunction and the velocity datum `∇^⊥ψ(0) = P_c v₀`
    (∀ c q η : ℝ, trainStream c (q, η) =
      -2 * ∑' n : ℤ, Real.exp (-((q - n * c) ^ 2 + η ^ 2) / 4)) ∧
    (∀ c : ℝ, c ≠ 0 → GaussianVortex.perpendicularGradient (trainStream c) =
      B0140.trainVelocity c) ∧
    -- finite weighted moments of the Gaussian data
    (∀ c : ℝ, 0 < c → ∀ (j : ℕ) (m : ℝ) (p : ℕ), 1 ≤ p →
      IntegrableOn (fun z => Cyl.ρc z ^ m * ‖iteratedFDeriv ℝ j (trainDatum c) z‖ ^ p)
        (Cyl.cell c)) ∧
    (∀ c : ℝ, 0 < c → ∀ (m : ℝ) (p : ℕ), 1 ≤ p →
      IntegrableOn (fun z => Cyl.ρc z ^ m * |Cyl.curl (trainDatum c) z| ^ p) (Cyl.cell c)) ∧
    -- the actual train `(V_c, E_c)`
    (∀ ν c : ℝ, 1 ≤ c → ∀ tr : TrainSol ν c,
      -- exact 2D Navier–Stokes evolution of the periodized datum
      IsTrain ν c (Vc tr) tr.p tr.ψ ∧
      (∀ s : ℝ, 0 ≤ s → ContDiff ℝ ∞ (Vc tr s)) ∧
      (∀ s z, Ec tr s z = Cyl.curl (Vc tr s) z) ∧
      (∀ s : ℝ, 0 < s → ∀ z, deriv (fun t => Ec tr t z) s +
        (Vc tr s z 0 * Cyl.partialQ (Ec tr s) z + Vc tr s z 1 * Cyl.partialEta (Ec tr s) z) -
        ν * Train.lapS (Ec tr s) z = 0) ∧
      (∀ z, Vc tr 0 z = toVec (∑' n : ℤ, velocity (z.1 - n * c, z.2))) ∧
      (∀ q η : ℝ, tr.ψ 0 (q, η) = -2 * ∑' n : ℤ, Real.exp (-((q - n * c) ^ 2 + η ^ 2) / 4)) ∧
      (∀ z, Ec tr 0 z = Gaussian.periodize c vorticity z) ∧
      -- finite weighted moments of its data
      (∀ (j : ℕ) (m : ℝ) (p : ℕ), 1 ≤ p →
        IntegrableOn (fun z => Cyl.ρc z ^ m * ‖iteratedFDeriv ℝ j (Vc tr 0) z‖ ^ p)
          (Cyl.cell c)) ∧
      (∀ (m : ℝ) (p : ℕ), 1 ≤ p →
        IntegrableOn (fun z => Cyl.ρc z ^ m * |Ec tr 0 z| ^ p) (Cyl.cell c)) ∧
      -- odd velocity and even vorticity under `(q, η) ↦ (-q, -η)`
      (∀ s : ℝ, 0 ≤ s → ∀ z, Vc tr s (-z) = -Vc tr s z) ∧
      (∀ s : ℝ, 0 ≤ s → ∀ z, Ec tr s (-z) = Ec tr s z) ∧
      -- zero circulation: of the data, and at every age under the `L¹` hypothesis
      (IntegrableOn (Ec tr 0) (Cyl.cell c) ∧ ∫ z in Cyl.cell c, Ec tr 0 z = 0) ∧
      (VorticityIntegrable tr → ∀ s : ℝ, 0 ≤ s →
        IntegrableOn (Ec tr s) (Cyl.cell c) ∧ ∫ z in Cyl.cell c, Ec tr s z = 0)) := by
  refine ⟨cell_eq, B0140.trainStream_apply, fun c hc => B0140.perpendicularGradient_trainStream hc,
    fun c hc j m p hp => integrableOn_weight_jet_trainDatum hc j m hp,
    fun c hc m p hp => integrableOn_weight_curl_trainDatum hc m hp,
    fun ν c hc tr => ?_⟩
  have hc0 : 0 < c := lt_of_lt_of_le one_pos hc
  exact ⟨isTrain_Vc tr, fun s hs => contDiff_Vc tr hs, fun s z => rfl,
    fun s hs z => Ec_vorticity_equation tr hs z, Vc_zero_apply tr,
    stream_zero tr hc, Ec_zero tr hc0.ne', fun j m p hp => moments_Vc_zero tr hc0 j m hp,
    fun m p hp => moments_Ec_zero tr hc0 m hp, fun s hs z => Vc_odd tr hs z,
    fun s hs z => Ec_even tr hs z, ⟨integrableOn_Ec_zero tr hc0, zero_circulation_zero tr hc0⟩,
    fun hL1 s hs => ⟨integrableOn_Ec tr hc0 hL1 hs, zero_circulation tr hc0 hL1 hs⟩⟩

end UnforcedLeray.B0238
