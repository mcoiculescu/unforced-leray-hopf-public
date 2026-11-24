import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_flatset_col_7_1_1_2_4_2_proj2

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ContDiff

namespace UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst

open UnforcedLeray.Short.IIIa (P0C P0re P0im toL2v reVec imVec cplxOf vnorm2)

theorem toL2v_reVec_zero (c : ℝ) :
    toL2v c (reVec (fun _ _ => (0 : ℂ))) = 0 := by
  have h : reVec (fun _ _ => (0 : ℂ)) = fun _ => (0 : UnforcedLeray.Cyl.Vec2) := by
    funext x; ext i; fin_cases i <;> simp [reVec, UnforcedLeray.Cyl.vec]
  rw [h]
  unfold toL2v
  split_ifs with hm
  · exact MemLp.toLp_zero hm
  · rfl

theorem toL2v_imVec_zero (c : ℝ) :
    toL2v c (imVec (fun _ _ => (0 : ℂ))) = 0 := by
  have h : imVec (fun _ _ => (0 : ℂ)) = fun _ => (0 : UnforcedLeray.Cyl.Vec2) := by
    funext x; ext i; fin_cases i <;> simp [imVec, UnforcedLeray.Cyl.vec]
  rw [h]
  unfold toL2v
  split_ifs with hm
  · exact MemLp.toLp_zero hm
  · rfl

/-- `P0C c 0 = 0` a.e. on the cell. -/
theorem p0C_zero_ae (c : ℝ) :
    P0C c (fun _ _ => (0 : ℂ)) =ᵐ[UnforcedLeray.Cyl.cellμ c] fun _ _ => (0 : ℂ) := by
  have h0 : (0 : UnforcedLeray.Cyl.L2v c) =ᵐ[UnforcedLeray.Cyl.cellμ c] 0 := Lp.coeFn_zero _ _ _
  filter_upwards [h0] with x hx
  funext i
  simp only [P0C, UnforcedLeray.Short.IIIa.P0re, UnforcedLeray.Short.IIIa.P0im, toL2v_reVec_zero,
    toL2v_imVec_zero, cplxOf, map_zero]
  rw [hx]
  simp


/-- **(1) Smooth representative of one projected slice** (source 1650-1656, 1676, 1684-1689: `P₀`
is an order-zero Fourier multiplier in `(q, η)` commuting with `∂_q, ∂_η`; the field `φ` is `C^∞`,
`c`-periodic, vanishing for `|η| > L`).  There is a `C^∞`, `c`-periodic, bounded `H` equal to
`P0C c φ` a.e. on the cell.  Route: `IIIa.p0CommWeakC` iterated gives `P0 φ ∈ H^k(cell)` for all `k`,
then a Sobolev embedding on the cylinder, or the explicit Fourier formula `P₀φ = φ - ∇p`. -/
def P0SliceSmooth : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ φ : ℝ × ℝ → Fin 2 → ℝ, (∀ i, ContDiff ℝ ∞ fun y => φ y i) →
    (∀ q η, φ (q + c, η) = φ (q, η)) → (∃ L : ℝ, ∀ y : ℝ × ℝ, φ y ≠ 0 → |y.2| ≤ L) →
    ∃ H : ℝ × ℝ → Fin 2 → ℂ, (∀ i, ContDiff ℝ ∞ fun y => H y i) ∧
      (∀ q η, H (q + c, η) = H (q, η)) ∧ (∃ C' : ℝ, ∀ y, vnorm2 (H y) ≤ C') ∧
      H =ᵐ[UnforcedLeray.Cyl.cellμ c] P0C c (fun y i => ((φ y i : ℝ) : ℂ))

/-- **(2) A jointly measurable representative of the projected slices** (source 3427-3440 /
1684-1689): `σ ↦ P0 Re F(σ), P0 Im F(σ)` are `L²(cell)`-continuous on `(0,∞)` (`IIIa.lerayClassCont`
for the nice family `F`), so `IIIa.jointRepVecC` gives a jointly measurable `J` with
`J(σ, ·) = P0C c (F(σ, ·))` a.e. on the cell for every `σ > 0`. -/
def P0JointRep : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ F : ℝ × (ℝ × ℝ) → Fin 2 → ℝ, (∀ i, ContDiff ℝ ∞ fun p => F p i) →
    (∀ s q η, F (s, (q + c, η)) = F (s, (q, η))) →
    (∃ s0 s1 L : ℝ, 0 < s0 ∧ ∀ p, F p ≠ 0 → p.1 ∈ Icc s0 s1 ∧ |p.2.2| ≤ L) →
    ∃ J : ℝ × (ℝ × ℝ) → Fin 2 → ℂ, (∀ i, Measurable fun p => J p i) ∧
      ∀ σ : ℝ, 0 < σ → (fun y => J (σ, y)) =ᵐ[UnforcedLeray.Cyl.cellμ c]
        P0C c (fun y i => ((F (σ, y) i : ℝ) : ℂ))

/-- **(3) The continuous representative of a measurable family of slices is measurable in the
parameter** (pure measure theory).  If `J` is jointly measurable and for each `σ > 0` the slice
`J(σ, ·)` agrees a.e. on the cell with a continuous `c`-periodic `H_σ`, then there is a jointly
measurable `Ψ` with `Ψ(σ, ·) = H` everywhere whenever `H` is a continuous `c`-periodic function with
`J(σ, ·) = H` a.e. on the cell.  Route: periodise `J` in `q` (`q ↦ q - c⌊q/c + 1/2⌋`), set `A_n(σ,y)` =
average of the periodised `J(σ,·)` over the square of half-side `1/n` about `y` (jointly measurable by
Fubini/`StronglyMeasurable.integral_prod_right`, slices locally integrable since a.e. equal to a
continuous function), and `Ψ = lim A_n` where the limit exists, `0` elsewhere
(`measurableSet_exists_tendsto`); for continuous `H` the averages converge to `H(y)` everywhere. -/
def ContRepMeasurable : Prop :=
  ∀ (c : ℝ), 0 < c → ∀ J : ℝ × (ℝ × ℝ) → Fin 2 → ℂ, (∀ i, Measurable fun p => J p i) →
    (∀ σ : ℝ, 0 < σ → ∃ H : ℝ × ℝ → Fin 2 → ℂ, Continuous H ∧
      (∀ q η, H (q + c, η) = H (q, η)) ∧
      (fun y => J (σ, y)) =ᵐ[UnforcedLeray.Cyl.cellμ c] H) →
    ∃ Ψ : ℝ × (ℝ × ℝ) → Fin 2 → ℂ, (∀ i, Measurable fun p => Ψ p i) ∧
      ∀ σ : ℝ, 0 < σ → ∀ H : ℝ × ℝ → Fin 2 → ℂ, Continuous H →
        (∀ q η, H (q + c, η) = H (q, η)) →
        (fun y => J (σ, y)) =ᵐ[UnforcedLeray.Cyl.cellμ c] H → ∀ y, Ψ (σ, y) = H y

theorem p0SmoothFamily_of (h1 : P0SliceSmooth) (h2 : P0JointRep) (h3 : ContRepMeasurable) :
    P0SmoothFamily := by
  intro c hc F hFs hFp hband
  obtain ⟨J, hJm, hJ⟩ := h2 c hc F hFs hFp hband
  obtain ⟨s0, s1, L, hs0, hb⟩ := hband
  have hzero : ∀ σ : ℝ, σ ≤ 0 → ∀ y : ℝ × ℝ, F (σ, y) = 0 := by
    intro σ hσ y
    by_contra hne
    have := (hb _ hne).1
    simp only [mem_Icc] at this
    linarith [this.1]
  -- slice data
  have hslice : ∀ σ : ℝ, ∃ H : ℝ × ℝ → Fin 2 → ℂ, (∀ i, ContDiff ℝ ∞ fun y => H y i) ∧
      (∀ q η, H (q + c, η) = H (q, η)) ∧ (∃ C' : ℝ, ∀ y, vnorm2 (H y) ≤ C') ∧
      H =ᵐ[UnforcedLeray.Cyl.cellμ c] P0C c (fun y i => ((F (σ, y) i : ℝ) : ℂ)) := by
    intro σ
    refine h1 c hc (fun y => F (σ, y)) (fun i => ?_) (fun q η => hFp σ q η) ⟨L, fun y hy => ?_⟩
    · exact (hFs i).comp (contDiff_const.prodMk contDiff_id)
    · exact (hb _ hy).2
  have hcont : ∀ H : ℝ × ℝ → Fin 2 → ℂ, (∀ i, ContDiff ℝ ∞ fun y => H y i) → Continuous H :=
    fun H hH => continuous_pi fun i => (hH i).continuous
  obtain ⟨Ψ0, hΨ0m, hΨ0⟩ := h3 c hc J hJm (fun σ hσ => by
    obtain ⟨H, hHs, hHp, -, hHae⟩ := hslice σ
    exact ⟨H, hcont H hHs, hHp, (hJ σ hσ).trans hHae.symm⟩)
  have key : ∀ σ : ℝ, 0 < σ → ∃ H : ℝ × ℝ → Fin 2 → ℂ, (∀ i, ContDiff ℝ ∞ fun y => H y i) ∧
      (∀ q η, H (q + c, η) = H (q, η)) ∧ (∃ C' : ℝ, ∀ y, vnorm2 (H y) ≤ C') ∧
      H =ᵐ[UnforcedLeray.Cyl.cellμ c] P0C c (fun y i => ((F (σ, y) i : ℝ) : ℂ)) ∧
      ∀ y, Ψ0 (σ, y) = H y := by
    intro σ hσ
    obtain ⟨H, hHs, hHp, hHb, hHae⟩ := hslice σ
    exact ⟨H, hHs, hHp, hHb, hHae, hΨ0 σ hσ H (hcont H hHs) hHp ((hJ σ hσ).trans hHae.symm)⟩
  refine ⟨fun p => if 0 < p.1 then Ψ0 p else 0, fun i => ?_, ?_, ?_⟩
  · have : (fun p : ℝ × (ℝ × ℝ) => (if 0 < p.1 then Ψ0 p else 0) i) =
        fun p => if 0 < p.1 then Ψ0 p i else 0 := by
      funext p; split_ifs <;> rfl
    rw [this]
    exact Measurable.ite (measurableSet_lt measurable_const measurable_fst) (hΨ0m i)
      measurable_const
  · intro s q η
    by_cases hs : 0 < s
    · obtain ⟨H, -, hHp, -, -, hH⟩ := key s hs
      simp only [hs, if_true]
      rw [hH, hH, hHp]
    · simp only [hs, if_false]
  · intro σ
    by_cases hσ : 0 < σ
    · obtain ⟨H, hHs, -, hHb, hHae, hH⟩ := key σ hσ
      simp only [hσ, ite_true, hH]
      refine ⟨hHs, hHb, ?_, hHae⟩
      intro hF0 y
      have hz : (fun y i => ((F (σ, y) i : ℝ) : ℂ)) = fun _ _ => (0 : ℂ) := by
        funext y' i; rw [hF0 y']; simp
      have hae : (fun y => J (σ, y)) =ᵐ[UnforcedLeray.Cyl.cellμ c] fun _ _ => (0 : ℂ) := by
        have := hJ σ hσ
        rw [hz] at this
        exact this.trans (p0C_zero_ae c)
      have := hΨ0 σ hσ (fun _ _ => (0 : ℂ)) continuous_const (fun _ _ => rfl) hae y
      rw [← hH y, this]
      rfl
    · simp only [hσ, ite_false]
      refine ⟨fun i => contDiff_const, ⟨0, fun y => ?_⟩, fun _ _ => trivial, ?_⟩
      · simp [vnorm2]
      · have hz : (fun y i => ((F (σ, y) i : ℝ) : ℂ)) = fun _ _ => (0 : ℂ) := by
          funext y' i; rw [hzero σ (not_lt.mp hσ) y']; simp
        rw [hz]
        exact (p0C_zero_ae c).symm

end UnforcedLeray.Short.PartIIIb.Concrete.FlatSettingInst
