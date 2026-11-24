import UnforcedLeray.Short.PartIIIb.Sub.IIIb_D2_3_2.Ward3

/-!
# `WardIBP` from five integration-by-parts facts (source 4268-4270)

Source: `the November 2 reference manuscript`.
All pairings are against a phase test `Φ` of bounded spatial support, so no decay of `H, Y, E`
is needed: only smoothness (and periodicity of `H`).  The five facts are

* `IBPAdjoint` (source 4268, `L₀ᵗ` is the transpose of `L₀ = T₀ - νΔ - ½` against a phase test; the
  `τ`-term is killed by periodicity, the spatial terms by compact support in `y`);
* `IBPBridge` (source 4140-4141: `D_μ = L₀ + μ` on the complexified real field);
* `IBPDiv` (source 4268-4270: `⟨div(a⊗b + b⊗a), Φ⟩ = -stressPair`);
* `IBPGrad` (source 4268-4270: the gradient term is killed by `div Φ = 0`);
* `IBPLin` (pairing is additive on continuous fields), `IBPCont` (continuity of the derived fields).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The complexified real field `x ↦ realC (F x.1 x.2)` on `ℝ × ℝ³`. -/
def realCf (F : ℝ → Space → Space) : ℝ × Space → CVec3 := fun x => B0412.realC (F x.1 x.2)

/-- (source 4268) `⟨L₀ᵗΦ + μΦ, u⟩ = ⟨Φ, L₀u + μu⟩` for smooth `P`-periodic `u` and a phase test `Φ`.
Proof: `lagrange_L0` (B0411) turns `L₀ᵗΦ·u - Φ·L₀u` into a `τ`-derivative and `y`-derivatives of
compactly supported `y`-bounded smooth functions; see `Short/PartII-b/Tasks/RawResidualFamily/
SmoothResidualWeakForm.lean` (`smoothResidualWeakForm_proof`, which does exactly this with the
lemmas `srwf_slab_dy`, `srwf_dotFn_isPhaseTest`, `B0005.integral_slab_dτ`). -/
def IBPAdjoint : Prop :=
  ∀ (P ν μ : ℝ), 0 < P → ∀ u : ℝ × Space → CVec3, ContDiff ℝ ∞ u →
    (∀ x : ℝ × Space, u (x.1 + P, x.2) = u x) →
    ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ →
      pairF P (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) u =
        pairF P Φ (fun x => L0 ν u x + (μ : ℂ) • u x)

/-- (source 4140-4141) `D_μ = L₀ + μ` on the complexified real field: pointwise calculus
(`deriv` in `τ`, `fderiv` in `y`, `dτ`, `radialT`, `lapT` of B0411). -/
def IBPBridge : Prop :=
  ∀ (ν μ : ℝ) (H : ℝ → Space → Space), ContDiff ℝ ∞ (fun x : ℝ × Space => H x.1 x.2) →
    ∀ x : ℝ × Space,
      L0 ν (realCf H) x + (μ : ℂ) • realCf H x = realCf (physDmu ν μ H) x

/-- (source 4268-4270) `⟨Φ, div(a⊗b + b⊗a)⟩ = -stressPair(a⊗b + b⊗a, Φ)`: `(div T)_i = Σ_j ∂_jT_ij`,
one integration by parts in `y_j` against compactly supported `Φ_i`. -/
def IBPDiv : Prop :=
  ∀ (P : ℝ) (U W : ℝ → Space → Space),
    ContDiff ℝ ∞ (fun x : ℝ × Space => U x.1 x.2) →
    ContDiff ℝ ∞ (fun x : ℝ × Space => W x.1 x.2) →
    ∀ Φ : ℝ × Space → CVec3, IsPhaseTest P Φ →
      pairF P Φ (realCf (fun τ y => physDivSym (U τ) (W τ) y)) =
        -stressPair P (fun x => symProd (U x.1 x.2) (W x.1 x.2)) Φ

/-- (source 4268-4270) the gradient term: `⟨Φ, ∇q⟩ = -⟨div Φ, q⟩ = 0`. -/
def IBPGrad : Prop :=
  ∀ (P : ℝ) (q : ℝ → Space → ℝ), ContDiff ℝ ∞ (fun x : ℝ × Space => q x.1 x.2) →
    ∀ Φ : ℝ × Space → CVec3, IsSolTest P Φ →
      pairF P Φ (realCf (fun τ y => physGrad (q τ) y)) = 0

/-- `pairF P Φ` is additive and subtractive on continuous fields, for a phase test `Φ`
(`Φ·u` is continuous with bounded `y`-support, hence integrable on the slab; use
`B0005.integrable_slab` and `integral_add`, as in `pairF_add_right_of_integrable`). -/
def IBPLin : Prop :=
  ∀ (P : ℝ) (Φ : ℝ × Space → CVec3), IsPhaseTest P Φ → ∀ u v : ℝ × Space → CVec3,
    Continuous u → Continuous v →
      pairF P Φ (fun x => u x + v x) = pairF P Φ u + pairF P Φ v ∧
      pairF P Φ (fun x => u x - v x) = pairF P Φ u - pairF P Φ v

/-- Continuity of the derived fields `∇q` and `div(a⊗b + b⊗a)` for smooth data (they are
compositions of `fderiv` of jointly smooth maps with continuous maps). -/
def IBPCont : Prop :=
  (∀ q : ℝ → Space → ℝ, ContDiff ℝ ∞ (fun x : ℝ × Space => q x.1 x.2) →
    Continuous (realCf (fun τ y => physGrad (q τ) y))) ∧
  (∀ U W : ℝ → Space → Space, ContDiff ℝ ∞ (fun x : ℝ × Space => U x.1 x.2) →
    ContDiff ℝ ∞ (fun x : ℝ × Space => W x.1 x.2) →
    Continuous (realCf (fun τ y => physDivSym (U τ) (W τ) y)))

theorem contDiff_realC_8 : ContDiff ℝ ∞ (fun x : Space => B0412.realC x) := by
  apply (contDiff_piLp 2).2
  intro i
  have hcoord : (fun x : Space => (B0412.realC x).ofLp i) =
      fun x : Space => ((x i : ℝ) : ℂ) := by
    funext x
    exact B0412.realC_apply x i
  rw [hcoord]
  exact Complex.ofRealCLM.contDiff.comp (contDiff_piLp_apply (p := 2) (i := i))

theorem contDiff_realCf {F : ℝ → Space → Space}
    (hF : ContDiff ℝ ∞ (fun x : ℝ × Space => F x.1 x.2)) : ContDiff ℝ ∞ (realCf F) :=
  contDiff_realC_8.comp hF

theorem realCf_add (F G : ℝ → Space → Space) :
    realCf (fun τ y => F τ y + G τ y) = fun x => realCf F x + realCf G x := by
  funext x
  ext i
  simp [realCf, B0412.realC_apply]

theorem realCf_sub (F G : ℝ → Space → Space) :
    realCf (fun τ y => F τ y - G τ y) = fun x => realCf F x - realCf G x := by
  funext x
  ext i
  simp [realCf, B0412.realC_apply]

/-- Pointwise additivity of `physDivSym` in the second slot. -/
theorem physDivSym_add {a b c : Space → Space} (ha : Differentiable ℝ a) (hb : Differentiable ℝ b)
    (hc : Differentiable ℝ c) (y : Space) :
    physDivSym a (fun y' => b y' + c y') y = physDivSym a b y + physDivSym a c y := by
  unfold physDivSym
  ext i
  simp only [PiLp.add_apply, WithLp.ofLp_add, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcoord : ∀ (f : Space → Space) (k : Fin 3), Differentiable ℝ f →
      Differentiable ℝ (fun y' => f y' k) := fun f k hf =>
    ((EuclideanSpace.proj k : Space →L[ℝ] ℝ).differentiable.comp hf)
  have d1 : Differentiable ℝ (fun y' => a y' j * b y' i + b y' j * a y' i) :=
    ((hcoord a j ha).mul (hcoord b i hb)).add ((hcoord b j hb).mul (hcoord a i ha))
  have d2 : Differentiable ℝ (fun y' => a y' j * c y' i + c y' j * a y' i) :=
    ((hcoord a j ha).mul (hcoord c i hc)).add ((hcoord c j hc).mul (hcoord a i ha))
  rw [← add_apply, ← fderiv_add d1.differentiableAt d2.differentiableAt]
  congr 2
  funext y'
  simp only [Pi.add_apply]
  ring

theorem wardIBP_of (hA : IBPAdjoint) (hB : IBPBridge) (hD : IBPDiv) (hG : IBPGrad)
    (hL : IBPLin) (hC : IBPCont) (ν μ P : ℝ) (hP : 0 < P) : WardIBP ν μ P := by
  intro U H Y E q hU hUp _ hq _ hF hid Φ hΦ
  have hH : ContDiff ℝ ∞ (fun x : ℝ × Space => H x.1 x.2) := (hF H (by simp)).1
  have hY : ContDiff ℝ ∞ (fun x : ℝ × Space => Y x.1 x.2) := (hF Y (by simp)).1
  have hE : ContDiff ℝ ∞ (fun x : ℝ × Space => E x.1 x.2) := (hF E (by simp)).1
  have hHp : ∀ τ y, H (τ + P) y = H τ y := (hF H (by simp)).2.2
  have hW : ContDiff ℝ ∞ (fun x : ℝ × Space => (Y x.1 x.2 + H x.1 x.2)) := hY.add hH
  -- the classical identity solved for `D_μ H`
  have hslice : ∀ (F : ℝ → Space → Space),
      ContDiff ℝ ∞ (fun x : ℝ × Space => F x.1 x.2) → ∀ τ,
      Differentiable ℝ (F τ) := by
    intro F hF' τ
    have : ContDiff ℝ ∞ (fun y : Space => F τ y) :=
      hF'.comp (contDiff_const.prodMk contDiff_id)
    exact this.differentiable (by simp)
  have hpt : ∀ τ y, physDmu ν μ H τ y =
      E τ y + physGrad (q τ) y - physDivSym (U τ) (fun y' => Y τ y' + H τ y') y := by
    intro τ y
    have h1 := hid τ y
    rw [physDivSym_add (hslice U hU τ) (hslice Y hY τ) (hslice H hH τ) y]
    have := congrArg (fun v => v) h1
    ext i
    have hi := congrArg (fun v => v i) h1
    simp only [PiLp.add_apply, PiLp.sub_apply] at hi ⊢
    linarith
  have hfun : physDmu ν μ H = fun τ y =>
      (E τ y + physGrad (q τ) y) - physDivSym (U τ) (fun y' => Y τ y' + H τ y') y := by
    funext τ y; exact hpt τ y
  have hΦt : IsPhaseTest P Φ := hΦ.1
  have hu : ContDiff ℝ ∞ (realCf H) := contDiff_realCf hH
  have hup : ∀ x : ℝ × Space, realCf H (x.1 + P, x.2) = realCf H x := by
    intro x; simp only [realCf, hHp]
  show pairF P (fun x => L0T ν Φ x + (μ : ℂ) • Φ x) (realCf H) =
    pairF P Φ (realCf E) + _
  -- step 1: adjoint and bridge
  have s1 := hA P ν μ hP (realCf H) hu hup Φ hΦt
  have s2 : (fun x => L0 ν (realCf H) x + (μ : ℂ) • realCf H x) =
      realCf (physDmu ν μ H) := funext (hB ν μ H hH)
  rw [s2, hfun] at s1
  rw [s1]
  -- step 2: split the right side
  have cE : Continuous (realCf E) := (contDiff_realCf hE).continuous
  have cG := hC.1 q hq
  have cD := hC.2 U (fun τ y => Y τ y + H τ y) hU hW
  have cEG : Continuous (fun x => realCf E x + realCf (fun τ y => physGrad (q τ) y) x) :=
    cE.add cG
  rw [show realCf (fun τ y => (E τ y + physGrad (q τ) y) -
      physDivSym (U τ) (fun y' => Y τ y' + H τ y') y) = fun x =>
      (realCf E x + realCf (fun τ y => physGrad (q τ) y) x) -
        realCf (fun τ y => physDivSym (U τ) (fun y' => Y τ y' + H τ y') y) x by
    rw [realCf_sub, realCf_add]]
  rw [(hL P Φ hΦt _ _ cEG cD).2, (hL P Φ hΦt _ _ cE cG).1, hG P q hq Φ hΦ,
    hD P U (fun τ y => Y τ y + H τ y) hU hW Φ hΦt]
  have hsym : (fun x : ℝ × Space => symProd (U x.1 x.2) (Y x.1 x.2 + H x.1 x.2)) =
      fun x => symProd (U x.1 x.2) (Y x.1 x.2 + H x.1 x.2) := rfl
  simp

end UnforcedLeray.Short.PartIIIb.Concrete
