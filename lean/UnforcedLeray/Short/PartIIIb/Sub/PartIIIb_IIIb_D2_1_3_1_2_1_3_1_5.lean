import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_IIIb_D2_1_3_1_2_1_3_1

/-!
# Leray density in `L²`: decomposition

Source `the November 2 reference manuscript`
lines 1351-1362, 1470-1480.  `h ∈ Y_2` weakly solenoidal and orthogonal to solenoidal tests.

Route.  (I) `curl A` is a solenoidal test for every phase test `A`, so `⟪curl A, h⟫ = 0`;
with `curl curl A = ∇ div A - Δ A` and weak solenoidality, `⟪Δ Θ, h⟫ = 0` for every vector
phase test `Θ`.  (II) Weyl in `L²` by an approximate identity (no Fourier): there is a radial
smooth compactly supported `b` with `∫ b = 1` and a radial smooth compactly supported `u` with
`Δu = b - b_{(2)}` (`b_{(s)}(z) = s⁻³ b(z/s)`).  Scaling and convolution in `y` give
`g(s) = ⟪Θ * b_{(s)}, h⟫ = g(2s)`; `g(s) → 0` as `s → ∞` (`‖Θ*b_{(s)}‖_{L²} ≲ s^{-3/2}`) and
`g(s) → ⟪Θ,h⟫` as `s → 0`, so `⟪Θ,h⟫ = 0`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology UnforcedLeray.Axi
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest)

/-- The scalar divergence `∑ⱼ ∂ⱼ Aⱼ` of a vector phase field. -/
def divT (A : ℝ × Space → CVec3) : ℝ × Space → ℂ := fun x => ∑ j : Fin 3, dy j A x j

/-- A smooth compactly supported kernel on `ℝ³`. -/
def KerOK (κ : Space → ℝ) : Prop := ContDiff ℝ ∞ κ ∧ HasCompactSupport κ

/-- Convolution in `y` only: `(κ * Θ)(τ, y) = ∫ κ(z) Θ(τ, y - z) dz`. -/
def convY (κ : Space → ℝ) (Θ : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun x => ∫ z, (κ z : ℂ) • Θ (x.1, x.2 - z)

/-- The mass-preserving dilation `κ_{(s)}(z) = s⁻³ κ(z/s)`. -/
def dilK (κ : Space → ℝ) (s : ℝ) : Space → ℝ := fun z => (s⁻¹) ^ 3 * κ (s⁻¹ • z)

/-- The potential dilation `u_{(s)}(z) = s⁻¹ u(z/s)` (so `Δ u_{(s)} = (Δu)_{(s)}`). -/
def dilU (u : Space → ℝ) (s : ℝ) : Space → ℝ := fun z => s⁻¹ * u (s⁻¹ • z)

/-- A function of `y` as a scalar phase field. -/
def liftS (u : Space → ℝ) : ℝ × Space → ℂ := fun x => (u x.2 : ℂ)

/-! ## Part (I): weak Laplace identity -/

/-- `curl A` is a solenoidal phase test for a phase test `A` (`div curl = 0` by `dy_dy_comm`). -/
def CurlIsSolTest : Prop :=
  ∀ (P : ℝ) (A : ℝ × Space → CVec3), IsPhaseTest P A → IsSolTest P (curlT A)

/-- The divergence of a vector phase test is a scalar phase test. -/
def DivIsPhaseTest : Prop :=
  ∀ (P : ℝ) (A : ℝ × Space → CVec3), IsPhaseTest P A → IsPhaseTest P (divT A)

/-- `curl curl A = ∇ div A - Δ A` for smooth `A` (derivatives in `y`). -/
def CurlCurlId : Prop :=
  ∀ A : ℝ × Space → CVec3, ContDiff ℝ ∞ A →
    curlT (curlT A) = fun x => gradT (divT A) x - lapT A x

/-- Linearity of the pairing in the test slot, for `h ∈ Y_2` (phase tests are bounded with
compact `y`-support, so the integrands are integrable). -/
def PairFSub : Prop :=
  ∀ (P : ℝ) (h : ℝ × Space → CVec3), UnforcedLeray.Short.IIb.IsInYr P 2 h →
    ∀ A B : ℝ × Space → CVec3, IsPhaseTest P A → IsPhaseTest P B →
      pairF P (fun x => A x - B x) h = pairF P A h - pairF P B h

/-- Weak harmonicity of `h` from weak solenoidality and orthogonality to solenoidal tests. -/
def WeakLaplaceOfSol : Prop :=
  ∀ (P : ℝ) (h : ℝ × Space → CVec3), UnforcedLeray.Short.IIb.IsInYr P 2 h →
    IsWeakSolenoidal P h → (∀ Ψ, IsSolTest P Ψ → pairF P Ψ h = 0) →
      ∀ Θ, IsPhaseTest P Θ → pairF P (lapT Θ) h = 0

theorem weakLaplaceOfSol_of (h1 : CurlIsSolTest) (h2 : DivIsPhaseTest) (h3 : CurlCurlId)
    (h4 : PairFSub) : WeakLaplaceOfSol := by
  intro P h hh hsol hann Θ hΘ
  have hA : IsPhaseTest P (curlT Θ) := (h1 P Θ hΘ).1
  have hB : IsPhaseTest P (gradT (divT Θ)) := (h2 P Θ hΘ).gradT
  have hC : IsPhaseTest P (curlT (curlT Θ)) := (h1 P _ hA).1
  have hid : lapT Θ = fun x => gradT (divT Θ) x - curlT (curlT Θ) x := by
    have := h3 Θ hΘ.smooth
    funext x
    rw [this]
    simp
  rw [hid, h4 P h hh _ _ hB hC, hsol _ (h2 P Θ hΘ), hann _ (h1 P _ hA)]
  simp

/-! ## Part (II): Weyl's lemma in `L²` by an approximate identity -/

/-- Radial potential: `b ≥ 0` radial-type bump of mass `1` and `u` with `Δu = b - b_{(2)}`
(`b(z) = β(|z|²)`, `u(z) = -½ ∫_1^2 s⁻² B(|z/s|²) ds`-type integral, `B' = -β`;
`div (y b_{(s)}) = -s ∂_s b_{(s)}`). -/
def RadialPotential : Prop :=
  ∃ b u : Space → ℝ, (∀ z, 0 ≤ b z) ∧ KerOK b ∧ KerOK u ∧ ∫ z, b z = 1 ∧
    ∀ x : ℝ × Space, lapT (liftS u) x = (((b x.2 - dilK b 2 x.2 : ℝ)) : ℂ)

/-- Dilations preserve smooth compact support. -/
def DilKerOK : Prop := ∀ (κ : Space → ℝ) (s : ℝ), KerOK κ → 0 < s → KerOK (dilK κ s) ∧ KerOK (dilU κ s)

/-- Scaling of the Laplacian: if `Δu₀ = b₀` then `Δ u₀_{(s)} = b₀_{(s)}`. -/
def DilLap : Prop :=
  ∀ (u₀ b₀ : Space → ℝ) (s : ℝ), KerOK u₀ → 0 < s →
    (∀ x : ℝ × Space, lapT (liftS u₀) x = ((b₀ x.2 : ℝ) : ℂ)) →
      ∀ x : ℝ × Space, lapT (liftS (dilU u₀ s)) x = ((dilK b₀ s x.2 : ℝ) : ℂ)

/-- Convolution in `y` with a smooth compactly supported kernel preserves phase tests. -/
def ConvTest : Prop :=
  ∀ (P : ℝ) (κ : Space → ℝ) (Θ : ℝ × Space → CVec3), KerOK κ → IsPhaseTest P Θ →
    IsPhaseTest P (convY κ Θ)

/-- `Δ_y (u * Θ) = (Δu) * Θ`. -/
def ConvLap : Prop :=
  ∀ (P : ℝ) (u c : Space → ℝ) (Θ : ℝ × Space → CVec3), KerOK u → KerOK c → IsPhaseTest P Θ →
    (∀ x : ℝ × Space, lapT (liftS u) x = ((c x.2 : ℝ) : ℂ)) → lapT (convY u Θ) = convY c Θ

/-- Linearity of `convY` in the kernel. -/
def ConvSub : Prop :=
  ∀ (P : ℝ) (κ₁ κ₂ : Space → ℝ) (Θ : ℝ × Space → CVec3), KerOK κ₁ → KerOK κ₂ → IsPhaseTest P Θ →
    convY (fun z => κ₁ z - κ₂ z) Θ = fun x => convY κ₁ Θ x - convY κ₂ Θ x

/-- Small scale: `⟪Θ * b_{(s)}, h⟫ → ⟪Θ, h⟫` as `s → 0+` (`Θ * b_{(s)} → Θ` uniformly with
uniformly bounded `y`-support, `∫ b = 1`; Cauchy–Schwarz against `h ∈ Y_2`). -/
def SmallScale : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ h : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 h →
    ∀ b : Space → ℝ, KerOK b → ∫ z, b z = 1 → ∀ Θ, IsPhaseTest P Θ →
      Tendsto (fun s : ℝ => pairF P (convY (dilK b s) Θ) h) (𝓝[>] 0) (𝓝 (pairF P Θ h))

/-- Large scale: `⟪Θ * b_{(s)}, h⟫ → 0` as `s → ∞` (`‖b_{(s)}‖_∞ ≲ s⁻³`, `y`-support radius
`≲ R + s`, so `‖Θ * b_{(s)}‖_{L²} ≲ s^{-3/2}`; Cauchy–Schwarz). -/
def LargeScale : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ h : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 h →
    ∀ b : Space → ℝ, KerOK b → ∀ Θ, IsPhaseTest P Θ →
      Tendsto (fun s : ℝ => pairF P (convY (dilK b s) Θ) h) atTop (𝓝 0)

/-- Weyl's lemma in `L²`: a weakly harmonic (in `y`) `h ∈ Y_2` annihilates all phase tests. -/
def WeylL2 : Prop :=
  ∀ (P : ℝ), 0 < P → ∀ h : ℝ × Space → CVec3, UnforcedLeray.Short.IIb.IsInYr P 2 h →
    (∀ Θ, IsPhaseTest P Θ → pairF P (lapT Θ) h = 0) → ∀ Θ, IsPhaseTest P Θ → pairF P Θ h = 0

theorem dilK_dilK (κ : Space → ℝ) (s t : ℝ) : dilK (dilK κ s) t = dilK κ (t * s) := by
  funext z
  simp only [dilK, smul_smul, mul_inv]
  rw [mul_pow, mul_assoc, mul_comm s⁻¹ t⁻¹]

theorem dilK_sub (κ c : Space → ℝ) (s : ℝ) :
    dilK (fun z => κ z - c z) s = fun z => dilK κ s z - dilK c s z := by
  funext z
  simp only [dilK, mul_sub]

theorem kerOK_sub {κ c : Space → ℝ} (hκ : KerOK κ) (hc : KerOK c) :
    KerOK (fun z => κ z - c z) :=
  ⟨hκ.1.sub hc.1, hκ.2.sub hc.2⟩

theorem weylL2_of (h1 : RadialPotential) (h2 : DilKerOK) (h3 : DilLap) (h4 : ConvTest)
    (h5 : ConvLap) (h6 : ConvSub) (h7 : SmallScale) (h8 : LargeScale) (h9 : PairFSub) :
    WeylL2 := by
  intro P hP h hh hlap Θ hΘ
  obtain ⟨b, u, hb0, hb, hu, hint, hlapu⟩ := h1
  set g : ℝ → ℂ := fun s => pairF P (convY (dilK b s) Θ) h with hg
  have hstep : ∀ s : ℝ, 0 < s → g s = g (s * 2) := by
    intro s hs
    have hb2 : KerOK (dilK b 2) := (h2 b 2 hb two_pos).1
    have hc : KerOK (fun z => b z - dilK b 2 z) := kerOK_sub hb hb2
    have hus : KerOK (dilU u s) := (h2 u s hu hs).2
    have hcs : KerOK (dilK (fun z => b z - dilK b 2 z) s) := (h2 _ s hc hs).1
    have hl := h3 u (fun z => b z - dilK b 2 z) s hu hs hlapu
    have hsb : KerOK (dilK b s) := (h2 b s hb hs).1
    have hsb2 : KerOK (dilK b (s * 2)) := (h2 b (s * 2) hb (by positivity)).1
    have hL := h5 P (dilU u s) (dilK (fun z => b z - dilK b 2 z) s) Θ hus hcs hΘ hl
    have hT := h4 P (dilU u s) Θ hus hΘ
    have h0 := hlap _ hT
    rw [hL] at h0
    have hd : dilK (fun z => b z - dilK b 2 z) s = fun z => dilK b s z - dilK b (s * 2) z := by
      rw [dilK_sub, dilK_dilK]
    rw [hd, h6 P _ _ Θ hsb hsb2 hΘ, h9 P h hh _ _ (h4 P _ Θ hsb hΘ) (h4 P _ Θ hsb2 hΘ)] at h0
    simp only [hg]
    exact sub_eq_zero.mp h0
  have hpow : ∀ s : ℝ, 0 < s → ∀ k : ℕ, g s = g (s * 2 ^ k) := by
    intro s hs k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ih, pow_succ, ← mul_assoc]
      exact hstep _ (by positivity)
  have hzero : ∀ s : ℝ, 0 < s → g s = 0 := by
    intro s hs
    have hlim : Tendsto (fun k : ℕ => g (s * 2 ^ k)) atTop (𝓝 0) :=
      (h8 P hP h hh b hb Θ hΘ).comp
        (Tendsto.const_mul_atTop hs (tendsto_pow_atTop_atTop_of_one_lt (by norm_num)))
    have hc : Tendsto (fun k : ℕ => g (s * 2 ^ k)) atTop (𝓝 (g s)) :=
      tendsto_const_nhds.congr (fun k => hpow s hs k)
    exact tendsto_nhds_unique hc hlim
  have hsm := h7 P hP h hh b hb hint Θ hΘ
  have h0 : Tendsto g (𝓝[>] 0) (𝓝 0) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => (hzero s hs).symm)
  exact tendsto_nhds_unique hsm h0

theorem lerayDensityL2_of (h1 : CurlIsSolTest) (h2 : DivIsPhaseTest) (h3 : CurlCurlId)
    (h4 : PairFSub) (h5 : WeylL2) : LerayDensityL2 := by
  intro P hP h hh hsol hann Θ hΘ
  exact h5 P hP h hh (weakLaplaceOfSol_of h1 h2 h3 h4 P h hh hsol hann) Θ hΘ

end UnforcedLeray.Short.PartIIIb.Concrete
