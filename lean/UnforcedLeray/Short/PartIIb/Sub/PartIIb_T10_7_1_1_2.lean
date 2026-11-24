import UnforcedLeray.Short.PartIIb.Sub.PartIIb_T10_7_1_1
import UnforcedLeray.Short.PartIIb.Tasks.ProfileGraphPhys.NvCInYr

/-!
# `PartII-b:T10/7/1/1/2` (`GLRotInv`): decomposition

Source of record: `the November 2 reference manuscript` lines 1912-1921
(`∂_ρ N_v b`, `∂_z N_v b` are `𝒪`-equivariant), 1639-1668 (chart).

Mathematics.  For `T ∈ 𝒪 = {R_θ, σ}` (a linear isometry of `ℝ³` fixing the axis pointwise and
preserving the horizontal plane) `N_v b(τ, T y) = T N_v b(τ, y)` off the axis (`GLNvEquivar`).
Differentiating, the gradient columns `g_j = ∂_j N_v b` satisfy
`g_j(τ, T y) = Σ_k T_{jk} T g_k(τ, y)` (`GLGradEquivar`: transport every phase test `Φ` to
`Ψ = T⁻¹ Φ(τ, T ·)`, use `Σ_k T_{jk} ∂_k Ψ = T⁻¹ (∂_j Φ)(T ·)` and `GLUniq`).  Specialising to the
radial combination and `e₃` (`T e₃ = e₃`, `T` preserves the horizontal plane and `ϱ`) gives the
equivariance of `radComb g` and `g 2` (`GLGradToEquivar`).
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff

namespace UnforcedLeray.Short.IIb

open UnforcedLeray.PhaseSpace UnforcedLeray.Cons.C03.Concrete

/-- The complexification of a real linear isometry `T` of `ℝ³` acting on `ℂ³`
(`T(a + i b) = T a + i T b`). -/
def cApp (T : Space ≃ₗᵢ[ℝ] Space) (v : CVec3) : CVec3 :=
  B0412.realC (T (reS v)) + Complex.I • B0412.realC (T (imS v))

/-- The group `𝒪` of Section "ring charts": the reflection `σ` and the rotations `R_θ` about `e₃`. -/
def GLIsO (T : Space ≃ₗᵢ[ℝ] Space) : Prop := T = Axi.reflY ∨ ∃ θ : ℝ, T = Axi.rotZ θ

/-- Transport of a field by `T`: `(T⁻¹ f(τ, T ·))`. -/
def trF (T : Space ≃ₗᵢ[ℝ] Space) (f : ℝ × Space → CVec3) : ℝ × Space → CVec3 :=
  fun x => cApp T.symm (f (x.1, T x.2))

/-- **(1) Equivariance of the lift** (SP 1912-1921): `N_v b(τ, T y) = T N_v b(τ, y)` for `T ∈ 𝒪`
and every profile `b`, almost everywhere.  Off the axis (a null set): `Axi.chart R τ (T y) =
Axi.chart R τ y` (`Axi.mer_map`, `Axi.age`, `Axi.trans` depend only on `mer y`, and `T y 2 = y 2`),
`Axi.frameL (T y) v = T (Axi.frameL y v)` (`Axi.eR_map`, `T e₃ = e₃`), then split `NvC` into
real and imaginary parts (`reS`/`imS` of `cApp`). -/
def GLNvEquivar : Prop :=
  ∀ (R : ℝ) (b : CProf) (T : Space ≃ₗᵢ[ℝ] Space), GLIsO T →
    ∀ᵐ x : ℝ × Space ∂volume, NvC R b (x.1, T x.2) = cApp T (NvC R b x)

/-- **(2) Phase tests are transported** by `T ∈ O(3)`: `T⁻¹ Φ(τ, T ·)` is smooth, `P`-periodic, and
vanishes for large `‖y‖` (`T` is an isometry). -/
def GLTestTransport : Prop :=
  ∀ (P : ℝ) (T : Space ≃ₗᵢ[ℝ] Space) (Φ : ℝ × Space → CVec3), IsPhaseTest P Φ →
    IsPhaseTest P (trF T Φ)

/-- **(3) The pairing is invariant** under the transport (`T` is measure preserving
(`LinearIsometryEquiv.measurePreserving`), `dotL (cApp T u) (cApp T v) = dotL u v`, so
`cApp T.symm` preserves `dotL`; `phaseInt` is a Lebesgue integral in `y`). -/
def GLPairTransport : Prop :=
  ∀ (P : ℝ) (T : Space ≃ₗᵢ[ℝ] Space) (Φ f : ℝ × Space → CVec3),
    pairF P Φ f = pairF P (trF T Φ) (trF T f)

/-- **(4) Chain rule for `dy` along the transport**: for smooth `Φ`,
`∂_j (T⁻¹ Φ(τ, T ·)) = T⁻¹ Σ_l (T e_j)_l (∂_l Φ)(τ, T ·)`. -/
def GLDyTransport : Prop :=
  ∀ (T : Space ≃ₗᵢ[ℝ] Space) (Φ : ℝ × Space → CVec3), ContDiff ℝ ∞ Φ → ∀ (j : Fin 3) (x : ℝ × Space),
    dy j (trF T Φ) x =
      cApp T.symm (∑ l : Fin 3, (((T (coordinateVector j)) l : ℝ) : ℂ) • dy l Φ (x.1, T x.2))

/-- **(5) `Y_r` is stable under the transport** (periodicity and measurability of the
composition with the measure-preserving map `id × T`, `phaseLpNorm` invariant). -/
def GLYrTransport : Prop :=
  ∀ (P r : ℝ) (T : Space ≃ₗᵢ[ℝ] Space) (f : ℝ × Space → CVec3), IsInYr P r f →
    IsInYr P r (trF T f)

/-- **(6)** `pairF P Φ ·` only sees the almost-everywhere class of the second argument. -/
def GLPairCongr : Prop :=
  ∀ (P : ℝ) (Φ f f' : ℝ × Space → CVec3), f =ᵐ[volume] f' → pairF P Φ f = pairF P Φ f'

/-- **(7a)** Linearity of `pairF P Φ ·` over a finite family of fields of `Y_r` (`r > 1`) against a
phase test (integrability: `Φ` is bounded with compact support in `y`, periodic in `τ`). -/
def GLPairLinR : Prop :=
  ∀ (P r : ℝ) (Φ : ℝ × Space → CVec3) (u : Fin 3 → ℝ × Space → CVec3) (a : Fin 3 → ℂ),
    0 < P → 1 < r → IsPhaseTest P Φ → (∀ k, IsInYr P r (u k)) →
      pairF P Φ (fun x => ∑ k, a k • u k x) = ∑ k, a k * pairF P Φ (u k)

/-- **(7b)** Linearity of `pairF P · w` over a finite family of phase tests, for `w ∈ Y_r`,
`r > 1`. -/
def GLPairLinL : Prop :=
  ∀ (P r : ℝ) (Φ : Fin 3 → ℝ × Space → CVec3) (w : ℝ × Space → CVec3) (a : Fin 3 → ℂ),
    0 < P → 1 < r → (∀ k, IsPhaseTest P (Φ k)) → IsInYr P r w →
      pairF P (fun x => ∑ k, a k • Φ k x) w = ∑ k, a k * pairF P (Φ k) w

/-- **(8) The gradient of an `𝒪`-equivariant field is equivariant** (SP 1912-1921): if
`w, g_j ∈ Y_r`, `∂_j w = g_j` weakly and `w(τ, T y) = T w(τ, y)` a.e., then
`g_j(τ, T y) = Σ_k T_{jk} T g_k(τ, y)` a.e. (`T_{jk} = (T e_k)_j`).
Proof: for a phase test `Φ`, `Ψ := trF T Φ` is a phase test (2); by (3),(6) and `w = trF T w` a.e.
`⟪-∂_jΦ, w⟫ = ⟪trF T (-∂_jΦ), w⟫ = Σ_k T_{jk} ⟪-∂_kΨ, w⟫ = Σ_k T_{jk} ⟪Ψ, g_k⟫ =
⟪Φ, Σ_k T_{jk} trF T⁻¹ g_k⟫` (4),(7); hence `GLUniq` (with (5)) gives
`g_j = Σ_k T_{jk} trF T.symm (g_k)` a.e. and one substitutes `x ↦ (τ, T y)` (measure preserving). -/
def GLGradEquivar : Prop :=
  ∀ (P r : ℝ) (w : ℝ × Space → CVec3) (g : Fin 3 → ℝ × Space → CVec3) (T : Space ≃ₗᵢ[ℝ] Space),
    0 < P → 1 < r → IsInYr P r w → (∀ j, IsInYr P r (g j)) →
    (∀ j, HasPtwOp P (fun Φ => -(dy j Φ)) w (g j)) →
    (∀ᵐ x : ℝ × Space ∂volume, w (x.1, T x.2) = cApp T (w x)) →
    ∀ᵐ x : ℝ × Space ∂volume, ∀ j : Fin 3,
      g j (x.1, T x.2) = ∑ k : Fin 3, (((T (coordinateVector k)) j : ℝ) : ℂ) • cApp T (g k x)

/-- **(9) From the gradient transformation law to the radial combination** (SP 1912-1921):
for `T ∈ 𝒪` (`T e₃ = e₃`, `T` preserves the horizontal plane: `T_{j2} = 0 = T_{2j}` for `j < 2`, and
`ϱ ∘ T = ϱ`) the law `g_j∘T = Σ_k T_{jk} T g_k` gives
`radComb g ∘ T = T radComb g` and `g 2 ∘ T = T g 2`; `reS`, `imS` commute with `cApp T`. -/
def GLGradToEquivar : Prop :=
  ∀ (g : Fin 3 → ℝ × Space → CVec3) (T : Space ≃ₗᵢ[ℝ] Space), GLIsO T →
    (∀ᵐ x : ℝ × Space ∂volume, ∀ j : Fin 3,
      g j (x.1, T x.2) = ∑ k : Fin 3, (((T (coordinateVector k)) j : ℝ) : ℂ) • cApp T (g k x)) →
    ∀ P : CVec3 → Space, (P = reS ∨ P = imS) →
      (∀ᵐ x : ℝ × Space ∂volume, P (radComb g (x.1, T x.2)) = T (P (radComb g x))) ∧
      (∀ᵐ x : ℝ × Space ∂volume, P (g 2 (x.1, T x.2)) = T (P (g 2 x)))

theorem gl_rotInv_of (hA : GLNvEquivar) (hB : GLGradEquivar) (hC : GLGradToEquivar) : GLRotInv := by
  intro c ε r b g hc hε hr1 hr3 hb hgY hgp P hP
  have hP0 : 0 < 2 * ε * c := by positivity
  have hN := nvCInYr_proof c ε r b hc hε (by linarith) hb
  have key : ∀ T : Space ≃ₗᵢ[ℝ] Space, GLIsO T →
      ∀ᵐ x : ℝ × Space ∂volume, ∀ j : Fin 3,
        g j (x.1, T x.2) = ∑ k : Fin 3, (((T (coordinateVector k)) j : ℝ) : ℂ) • cApp T (g k x) :=
    fun T hT => hB (2 * ε * c) r (NvC ε⁻¹ b) g T hP0 hr1 hN hgY hgp (hA ε⁻¹ b T hT)
  refine ⟨⟨fun θ => (hC g (Axi.rotZ θ) (Or.inr ⟨θ, rfl⟩) (key _ (Or.inr ⟨θ, rfl⟩)) P hP).1,
    (hC g Axi.reflY (Or.inl rfl) (key _ (Or.inl rfl)) P hP).1⟩,
    ⟨fun θ => (hC g (Axi.rotZ θ) (Or.inr ⟨θ, rfl⟩) (key _ (Or.inr ⟨θ, rfl⟩)) P hP).2,
    (hC g Axi.reflY (Or.inl rfl) (key _ (Or.inl rfl)) P hP).2⟩⟩

end UnforcedLeray.Short.IIb

#print axioms UnforcedLeray.Short.IIb.gl_rotInv_of
