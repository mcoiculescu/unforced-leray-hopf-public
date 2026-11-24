import UnforcedLeray.Short.PartIIIb.Sub.PartIIIb_C_near_pins_4

/-!
# `ChartDivPointwise`, decomposition (task `PartIII-b:C/near/pins/4/1`)

Source `the November 2 reference manuscript`:
1660-1665 (`div_ε` with the hoop traction), 3893-3897 (`div(√s b)` in the chart), 2683 (lifts
`𝒩_v b = √s b`, `𝒩_T T = sT`), 1640-1641, 2666-2668 (the chart `(τ, y) ↦ (s, q, η)`).

Route (all pieces are Props below; `chartDivPointwise_of` assembles them).  For a band tensor `M`
write `A = M_rr, B = sym M_rz, C = M_zz, D = M_φφ` (`cmpA .. cmpD`).  With `R = ε⁻¹`:
* `chartOf R c y τ` and the unreduced `Axi.chart R τ y` differ only by the `q`-period, so every
  `c`-periodic profile takes the same value at both (`PerReduceLeaf`);
* off the axis, for `F` differentiable at the chart point, `F ∘ chart` is jointly differentiable
  and `∂_v (F ∘ chart) = ϱD y v · ∂_ρ + v₃ · ∂_z` with `∂_ρ = √s (∂_q F - ε (2 s ∂_s F + η ∂_η F))`,
  `∂_z = √s ∂_η F` (`ChainLeaf`, from `Axi.radial_chain`, `Axi.axial_chain`, `Axi.chartD_apply`);
* the Cartesian divergence of `cylFrame · [[a,0,b],[0,d,0],[b,0,c]] · cylFrameᵀ` for axisymmetric
  data with radial/axial derivatives `(a_ρ, a_z)`, ... is `(u D_r, v D_r, D_z)` with `u = y₀/ϱ`,
  `v = y₁/ϱ`, `D_r = a_ρ + b_z + (a - d)/ϱ`, `D_z = b_ρ + c_z + b/ϱ` (`CylDivLeaf`);
* the real chart field `G0` has `merC G0 = s div_ε M` (`DivEpsRealLeaf`) and is `c`-periodic
  (`G0Periodic`); `∂_q, ∂_η, ∂_s` of `s · A` are `s ∂_q A`, `s ∂_η A`, `A + s ∂_s A`
  (`ScaleDeriv`).
-/

set_option autoImplicit false

noncomputable section

namespace UnforcedLeray.Short.PartIIIb.NearInst

open MeasureTheory UnforcedLeray.Axi UnforcedLeray.Short.PartIIIb.Concrete
  UnforcedLeray.Cons.C03.Concrete UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.B0220 (HSpace measureH Profile)
open UnforcedLeray.B0223 (MeridC)
open Set

/-- The `rr` component `A = M_rr` of a chart tensor. -/
def cmpA (M : Chart → Ten3) : Chart → ℝ := fun p => M p (0, 0)
/-- The symmetrised `rz` component `B = (M_rz + M_zr)/2`. -/
def cmpB (M : Chart → Ten3) : Chart → ℝ := fun p => symRZ (M p)
/-- The `zz` component `C = M_zz`. -/
def cmpC (M : Chart → Ten3) : Chart → ℝ := fun p => M p (2, 2)
/-- The `φφ` component `D = M_φφ`. -/
def cmpD (M : Chart → Ten3) : Chart → ℝ := fun p => M p (1, 1)

/-- The real chart field `s div_ε M` (source 1660-1665): radial component
`s (Q_ε A + ∂_η B - ε D)`, axial component `s (Q_ε B + ∂_η C)`, `Q_ε = ∂_q - ε (K + 1)`,
`K = 2 s ∂_s + η ∂_η`. -/
def G0 (ε : ℝ) (M : Chart → Ten3) (p : Chart) : Merid :=
  !₂[p.1 * (dQ (cmpA M) p - ε * (2 * p.1 * dS (cmpA M) p + p.2.2 * dEta (cmpA M) p + cmpA M p)
      + dEta (cmpB M) p - ε * cmpD M p),
    p.1 * (dQ (cmpB M) p - ε * (2 * p.1 * dS (cmpB M) p + p.2.2 * dEta (cmpB M) p + cmpB M p)
      + dEta (cmpC M) p)]

/-- `f` has radial derivative `ρd` and axial derivative `zd` at `x = (τ, y)`:
`∂_v f = ϱD_y(v) ρd + v₃ zd` for every direction `v` of `y`-space. -/
def RadDeriv (f : ℝ × Space → ℝ) (x : ℝ × Space) (ρd zd : ℝ) : Prop :=
  DifferentiableAt ℝ f x ∧
    ∀ v : Space, fderiv ℝ f x (0, v) = Axi.ϱD x.2 v * ρd + v 2 * zd

/-- **Periodic reduction** (source 2666-2668): a profile `c`-periodic in `q` takes the same value
at the reduced chart point `chartOf R c y τ` and at the unreduced `Axi.chart R τ y`
(`R log(ϱ/R) + Rτ/2 = Rτ/2 - (R/2) log(R²/ϱ²)` for `ϱ > 0`; on the axis both sides have
`log 0 = 0`). -/
def PerReduceLeaf : Prop :=
  ∀ (c R : ℝ), 0 < c → 0 < R → ∀ (E : Type) (f : Chart → E),
    (∀ s q η : ℝ, f (s, (q + c, η)) = f (s, (q, η))) →
    ∀ (τ : ℝ) (y : Space), f (chartOf R c y τ) = f (Axi.chart R τ y)

/-- **Chain rule through the chart** (source 2073-2075, 3755-3757; `Axi.radial_chain`,
`Axi.axial_chain`, `Axi.chartD_apply`, joint differentiability of the chart
`IIb.chartAdv_chart_diffAt`): off the axis, `F ∘ chart` is jointly differentiable in `(τ, y)` and
its spatial derivative in direction `v` is `ϱD_y(v) ∂_ρ + v₃ ∂_z`. -/
def ChainLeaf : Prop :=
  ∀ (R τ : ℝ) (y : Space), 0 < R → y ∉ Axi.axis → ∀ F : Chart → ℝ,
    DifferentiableAt ℝ F (Axi.chart R τ y) → ∀ p : Chart, p = Axi.chart R τ y →
    DifferentiableAt ℝ (fun x : ℝ × Space => F (Axi.chart R x.1 x.2)) (τ, y) ∧
    ∀ v : Space, fderiv ℝ (fun x : ℝ × Space => F (Axi.chart R x.1 x.2)) (τ, y) (0, v) =
      Axi.ϱD y v * (√(Axi.age R y) * (dQ F p - R⁻¹ *
        (2 * Axi.age R y * dS F p + Axi.trans R y * dEta F p))) +
      v 2 * (√(Axi.age R y) * dEta F p)

/-- **Cartesian divergence in cylindrical components** (source 1660-1665, 3893-3897: the term
`(T_rr - T_φφ)/ϱ` is the hoop traction): for axisymmetric no-swirl data `a, b, c, d`
(`T_rr, T_rz = T_zr, T_zz, T_φφ`) with radial/axial derivatives `(a_ρ, a_z)`, ..., the Cartesian
divergence `∑_j ∂_{y_j} T_ij` of `T = cylFrame · [[a,0,b],[0,d,0],[b,0,c]] · cylFrameᵀ` at
`(τ, y)`, `ϱ > 0`, is `(u D_r, v D_r, D_z)` with `u = y₀/ϱ`, `v = y₁/ϱ`,
`D_r = a_ρ + b_z + (a - d)/ϱ`, `D_z = b_ρ + c_z + b/ϱ`.  Sketch: the entries are
`T = a e_r e_rᵀ + d e_φ e_φᵀ + b (e_r e_zᵀ + e_z e_rᵀ) + c e_z e_zᵀ`; use
`∂_j u = (δ_{j1} - u ϱD(e_j))/ϱ`-type formulas (`Axi.eRD_apply_coord`, `Axi.hasFDerivAt_eR`),
`ϱD y e_j = (y₀/ϱ, y₁/ϱ, 0)_j`, the product rule and `RadDeriv`; the `d_ρ` terms cancel. -/
def CylDivLeaf : Prop :=
  ∀ (τ : ℝ) (y : Space), 0 < hRad y → ∀ (a b c d : ℝ × Space → ℝ)
    (aρ az bρ bz cρ cz dρ dz : ℝ),
    RadDeriv a (τ, y) aρ az → RadDeriv b (τ, y) bρ bz → RadDeriv c (τ, y) cρ cz →
    RadDeriv d (τ, y) dρ dz → ∀ i : Fin 3,
    ∑ j : Fin 3, dy j (fun x : ℝ × Space =>
      (((cylFrame x.2 * !![a x, 0, b x; 0, d x, 0; b x, 0, c x] * (cylFrame x.2).transpose) i j :
        ℝ) : ℂ)) (τ, y) =
      ((![y 0 / hRad y * (aρ + bz + (a (τ, y) - d (τ, y)) / hRad y),
          y 1 / hRad y * (aρ + bz + (a (τ, y) - d (τ, y)) / hRad y),
          bρ + cz + b (τ, y) / hRad y] i : ℝ) : ℂ)

/-- **Derivatives of the horizontal unit vector** (input of `CylDivLeaf`): off the axis
`u = y₀/ϱ`, `v = y₁/ϱ` are differentiable with `∂_0 u = v²/ϱ`, `∂_1 u = -uv/ϱ`, `∂_0 v = -uv/ϱ`,
`∂_1 v = u²/ϱ`, `∂_2 = 0` (`Axi.hasFDerivAt_eR`, `Axi.eRD_apply_coord`, or direct quotient rule
with `Axi.hasFDerivAt_ϱ`). -/
def UVDerivLeaf : Prop :=
  ∀ y : Space, 0 < hRad y →
    DifferentiableAt ℝ (fun z : Space => z 0 / hRad z) y ∧
    DifferentiableAt ℝ (fun z : Space => z 1 / hRad z) y ∧
    (∀ w : Space, fderiv ℝ (fun z : Space => z 0 / hRad z) y w =
      (y 1 / hRad y) ^ 2 / hRad y * w 0 - (y 0 / hRad y) * (y 1 / hRad y) / hRad y * w 1) ∧
    (∀ w : Space, fderiv ℝ (fun z : Space => z 1 / hRad z) y w =
      -((y 0 / hRad y) * (y 1 / hRad y) / hRad y) * w 0 + (y 0 / hRad y) ^ 2 / hRad y * w 1)

/-- The four components of the tensor of an `IsTensorTest` are smooth and `c`-periodic in `q`
(they are the real parts of the entries of `tv4 ∘ M`; `nsSym (M p)` depends only on them). -/
def CompSmoothLeaf : Prop :=
  ∀ (c : ℝ) (M : Chart → Ten3),
    UnforcedLeray.Short.PartIIa.IsTensorTest c (fun x => tv4 (M x)) →
    (∀ f ∈ ({cmpA M, cmpB M, cmpC M, cmpD M} : Set (Chart → ℝ)),
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) f ∧ ∀ s q η : ℝ, f (s, (q + c, η)) = f (s, (q, η)))

/-- `merC (G0) = s div_ε M` (source 1660-1665): `divEps` unfolds to
`Q_ε (tv4 M)₀ + ∂_η (tv4 M)₁ - ε (tv4 M)₃`, `Q_ε (tv4 M)₁ + ∂_η (tv4 M)₂` with
`opQ ε f = ∂_q f - ε (2 s ∂_s f + η ∂_η f + f)`; the complex derivatives of the entries
`((A p : ℝ) : ℂ)` are the real derivatives (`HasFDerivAt` through `Complex.ofRealCLM`). -/
def DivEpsRealLeaf : Prop :=
  ∀ (c ε : ℝ) (M : Chart → Ten3),
    UnforcedLeray.Short.PartIIa.IsTensorTest c (fun x => tv4 (M x)) →
    ∀ p : Chart, merC (G0 ε M p) =
      (p.1 : ℂ) • UnforcedLeray.Short.PartIIa.divEps ε (fun y => tv4 (M y)) p

/-- `G0` is `c`-periodic in `q` (the partial derivatives of a `c`-periodic smooth function are
`c`-periodic: differentiate `f ∘ shift = f`). -/
def G0Periodic : Prop :=
  ∀ (c ε : ℝ) (M : Chart → Ten3),
    UnforcedLeray.Short.PartIIa.IsTensorTest c (fun x => tv4 (M x)) →
    ∀ s q η : ℝ, G0 ε M (s, (q + c, η)) = G0 ε M (s, (q, η))

/-- Derivatives of `s · A`: `∂_q (sA) = s ∂_q A`, `∂_η (sA) = s ∂_η A`,
`∂_s (sA) = A + s ∂_s A` (product rule for `A` differentiable at `p`). -/
def ScaleDeriv : Prop :=
  ∀ (A : Chart → ℝ) (p : Chart), DifferentiableAt ℝ A p →
    dQ (fun p : Chart => p.1 * A p) p = p.1 * dQ A p ∧
    dEta (fun p : Chart => p.1 * A p) p = p.1 * dEta A p ∧
    dS (fun p : Chart => p.1 * A p) p = A p + p.1 * dS A p

/-! ## Assembly -/

theorem per_int {E : Type} (c : ℝ) (f : Chart → E)
    (h : ∀ s q η : ℝ, f (s, (q + c, η)) = f (s, (q, η))) :
    ∀ (k : ℤ) (s q η : ℝ), f (s, (q + k * c, η)) = f (s, (q, η)) := by
  intro k
  induction k using Int.induction_on with
  | zero => intro s q η; simp
  | succ n ih =>
    intro s q η
    have := h s (q + ((n : ℤ) : ℝ) * c) η
    have e : q + (((n : ℤ) + 1 : ℤ) : ℝ) * c = (q + ((n : ℤ) : ℝ) * c) + c := by push_cast; ring
    rw [e, this, ih]
  | pred n ih =>
    intro s q η
    have := h s (q + ((-(n : ℤ) - 1 : ℤ) : ℝ) * c) η
    rw [show q + ((-(n : ℤ) - 1 : ℤ) : ℝ) * c + c = q + ((-(n : ℤ) : ℤ) : ℝ) * c by
      push_cast; ring, ih] at this
    exact this.symm

theorem perExt_eq_of_per {c : ℝ} (f : Chart → Merid)
    (h : ∀ s q η : ℝ, f (s, (q + c, η)) = f (s, (q, η))) (p : Chart) :
    Axi.perExt c f p = f p := by
  obtain ⟨s, q, η⟩ := p
  simp only [Axi.perExt, Axi.cellRep]
  have := per_int c f h (-⌊(q + c / 2) / c⌋) s q η
  rw [← this]
  congr 3
  push_cast
  ring


theorem hRad_eq (y : Space) : hRad y = Axi.ϱ y := rfl

theorem notAxis_of_hRad {y : Space} (hy : 0 < hRad y) : y ∉ Axi.axis := by
  intro h
  obtain ⟨h0, h1⟩ := h
  have : hRad y = 0 := by simp [hRad, h0, h1]
  linarith

/-- the matrix identity behind `strPhys`. -/
theorem nsSym_eq (T : Ten3) :
    nsSym T = !![T (0, 0), 0, symRZ T; 0, T (1, 1), 0; symRZ T, 0, T (2, 2)] := rfl

theorem chartDivPointwise_of (h1 : PerReduceLeaf) (h2 : ChainLeaf) (h3 : CylDivLeaf)
    (h4 : CompSmoothLeaf) (h5 : DivEpsRealLeaf) (h6 : G0Periodic) (h7 : ScaleDeriv) :
    ChartDivPointwise := by
  intro c ε hc hε M hM
  refine ⟨G0 ε M, fun x => h5 c ε M hM x, ?_⟩
  intro τ y hy i
  have hR : 0 < ε⁻¹ := inv_pos.2 hε
  have hyax : y ∉ Axi.axis := notAxis_of_hRad hy
  obtain hcomp := h4 c M hM
  have hA := hcomp (cmpA M) (by simp)
  have hB := hcomp (cmpB M) (by simp)
  have hC := hcomp (cmpC M) (by simp)
  have hD := hcomp (cmpD M) (by simp)
  set fA : Chart → ℝ := fun p => p.1 * cmpA M p with hfA
  set fB : Chart → ℝ := fun p => p.1 * cmpB M p with hfB
  set fC : Chart → ℝ := fun p => p.1 * cmpC M p with hfC
  set fD : Chart → ℝ := fun p => p.1 * cmpD M p with hfD
  have hsm : ∀ g : Chart → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
      Differentiable ℝ (fun p : Chart => p.1 * g p) := fun g hg =>
    (contDiff_fst.mul hg).differentiable (by simp)
  -- Step A : global identity for the physical stress
  have hper : ∀ s q η : ℝ, (fun p : Chart => p.1 • nsSym (M p)) (s, (q + c, η)) =
      (fun p : Chart => p.1 • nsSym (M p)) (s, (q, η)) := by
    intro s q η
    simp only [nsSym_eq]
    have a1 := hA.2 s q η
    have a2 := hB.2 s q η
    have a3 := hC.2 s q η
    have a4 := hD.2 s q η
    simp only [cmpA, cmpB, cmpC, cmpD] at a1 a2 a3 a4
    rw [a1, a2, a3, a4]
  have hstr : ∀ x : ℝ × Space, strPhys ε⁻¹ c M x =
      cylFrame x.2 * !![fA (Axi.chart ε⁻¹ x.1 x.2), 0, fB (Axi.chart ε⁻¹ x.1 x.2);
        0, fD (Axi.chart ε⁻¹ x.1 x.2), 0; fB (Axi.chart ε⁻¹ x.1 x.2), 0,
        fC (Axi.chart ε⁻¹ x.1 x.2)] * (cylFrame x.2).transpose := by
    intro x
    have := h1 c ε⁻¹ hc hR (Matrix (Fin 3) (Fin 3) ℝ)
      (fun p : Chart => p.1 • nsSym (M p)) hper x.1 x.2
    simp only [strPhys, cartLift]
    rw [this]
    simp only [nsSym_eq]
    congr 2
    ext a b
    fin_cases a <;> fin_cases b <;> simp [hfA, hfB, hfC, hfD, cmpA, cmpB, cmpC, cmpD]
  -- Step B : derivative data
  have hdiff : ∀ g : Chart → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g →
      DifferentiableAt ℝ (fun p : Chart => p.1 * g p) (Axi.chart ε⁻¹ τ y) :=
    fun g hg => (hsm g hg).differentiableAt
  set p0 : Chart := Axi.chart ε⁻¹ τ y with hp0
  have hdA := hdiff _ hA.1
  have hdB := hdiff _ hB.1
  have hdC := hdiff _ hC.1
  have hdD := hdiff _ hD.1
  have hrad : ∀ F : Chart → ℝ, DifferentiableAt ℝ F p0 →
      RadDeriv (fun x : ℝ × Space => F (Axi.chart ε⁻¹ x.1 x.2)) (τ, y)
        (√(Axi.age ε⁻¹ y) * (dQ F p0 - ε⁻¹⁻¹ *
          (2 * Axi.age ε⁻¹ y * dS F p0 + Axi.trans ε⁻¹ y * dEta F p0)))
        (√(Axi.age ε⁻¹ y) * dEta F p0) := by
    intro F hF
    obtain ⟨hd, hv⟩ := h2 ε⁻¹ τ y hR hyax F hF p0 rfl
    exact ⟨hd, hv⟩
  have key := h3 τ y hy _ _ _ _ _ _ _ _ _ _ _ _ (hrad fA hdA) (hrad fB hdB) (hrad fC hdC)
    (hrad fD hdD) i
  have hlhs : ∑ j : Fin 3, dy j (fun x : ℝ × Space => ((strPhys ε⁻¹ c M x i j : ℝ) : ℂ)) (τ, y) =
      ∑ j : Fin 3, dy j (fun x : ℝ × Space =>
      (((cylFrame x.2 * !![fA (Axi.chart ε⁻¹ x.1 x.2), 0, fB (Axi.chart ε⁻¹ x.1 x.2);
        0, fD (Axi.chart ε⁻¹ x.1 x.2), 0; fB (Axi.chart ε⁻¹ x.1 x.2), 0,
        fC (Axi.chart ε⁻¹ x.1 x.2)] * (cylFrame x.2).transpose) i j : ℝ) : ℂ)) (τ, y) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    funext x
    rw [hstr x]
  rw [hlhs, key]
  have dAd : ∀ g : Chart → ℝ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → DifferentiableAt ℝ g p0 :=
    fun g hg => (hg.differentiable (by simp)) p0
  obtain ⟨sQA, sEA, sSA⟩ := h7 (cmpA M) p0 (dAd _ hA.1)
  obtain ⟨sQB, sEB, sSB⟩ := h7 (cmpB M) p0 (dAd _ hB.1)
  obtain ⟨sQC, sEC, sSC⟩ := h7 (cmpC M) p0 (dAd _ hC.1)
  have hρ : 0 < Axi.ϱ y := Axi.ϱ_pos hyax
  have hsq : √(Axi.age ε⁻¹ y) = ε⁻¹ / Axi.ϱ y := Axi.sqrt_age hR hyax
  have hinv : 1 / hRad y = ε * √(Axi.age ε⁻¹ y) := by
    rw [hsq, hRad_eq]; field_simp
  have hs1 : p0.1 = Axi.age ε⁻¹ y := rfl
  have hs2 : p0.2.2 = Axi.trans ε⁻¹ y := rfl
  have hfA0 : fA (Axi.chart ε⁻¹ τ y) = p0.1 * cmpA M p0 := rfl
  have hfB0 : fB (Axi.chart ε⁻¹ τ y) = p0.1 * cmpB M p0 := rfl
  have hfD0 : fD (Axi.chart ε⁻¹ τ y) = p0.1 * cmpD M p0 := rfl
  have hDr : √(Axi.age ε⁻¹ y) * (dQ fA p0 - ε * (2 * Axi.age ε⁻¹ y * dS fA p0 +
      Axi.trans ε⁻¹ y * dEta fA p0)) + √(Axi.age ε⁻¹ y) * dEta fB p0 +
      (fA (Axi.chart ε⁻¹ τ y) - fD (Axi.chart ε⁻¹ τ y)) / hRad y =
      √(Axi.age ε⁻¹ y) * (p0.1 * (dQ (cmpA M) p0 - ε * (2 * p0.1 * dS (cmpA M) p0 +
        p0.2.2 * dEta (cmpA M) p0 + cmpA M p0) + dEta (cmpB M) p0 - ε * cmpD M p0)) := by
    rw [hfA0, hfD0, div_eq_mul_one_div, hinv]
    simp only [hfA, hfB] at sQA sEA sSA sEB ⊢
    rw [sQA, sEA, sSA, sEB, hs1, hs2]
    ring
  have hDz : √(Axi.age ε⁻¹ y) * (dQ fB p0 - ε * (2 * Axi.age ε⁻¹ y * dS fB p0 +
      Axi.trans ε⁻¹ y * dEta fB p0)) + √(Axi.age ε⁻¹ y) * dEta fC p0 +
      fB (Axi.chart ε⁻¹ τ y) / hRad y =
      √(Axi.age ε⁻¹ y) * (p0.1 * (dQ (cmpB M) p0 - ε * (2 * p0.1 * dS (cmpB M) p0 +
        p0.2.2 * dEta (cmpB M) p0 + cmpB M p0) + dEta (cmpC M) p0)) := by
    rw [hfB0, div_eq_mul_one_div, hinv]
    simp only [hfB, hfC] at sQB sEB sSB sEC ⊢
    rw [sQB, sEB, sSB, sEC, hs1, hs2]
    ring
  have hperG := perExt_eq_of_per (G0 ε M) (h6 c ε M hM)
  have hGp : G0 ε M p0 = !₂[_, _] := rfl
  have hDr' : √(Axi.age ε⁻¹ y) * (dQ fA p0 - ε * (2 * Axi.age ε⁻¹ y * dS fA p0 +
      Axi.trans ε⁻¹ y * dEta fA p0)) + √(Axi.age ε⁻¹ y) * dEta fB p0 +
      (fA (Axi.chart ε⁻¹ τ y) - fD (Axi.chart ε⁻¹ τ y)) / hRad y =
      √(Axi.age ε⁻¹ y) * (G0 ε M p0) 0 := hDr
  have hDz' : √(Axi.age ε⁻¹ y) * (dQ fB p0 - ε * (2 * Axi.age ε⁻¹ y * dS fB p0 +
      Axi.trans ε⁻¹ y * dEta fB p0)) + √(Axi.age ε⁻¹ y) * dEta fC p0 +
      fB (Axi.chart ε⁻¹ τ y) / hRad y = √(Axi.age ε⁻¹ y) * (G0 ε M p0) 1 := hDz
  have hvec : ∀ (Gr Gz : ℝ) (i : Fin 3),
      ![y 0 / hRad y * (√(Axi.age ε⁻¹ y) * Gr), y 1 / hRad y * (√(Axi.age ε⁻¹ y) * Gr),
        √(Axi.age ε⁻¹ y) * Gz] i =
      (√(Axi.age ε⁻¹ y) • (Gr • Axi.eR y + Gz • Axi.e3)) i := by
    intro Gr Gz i
    fin_cases i <;> simp [hRad_eq] <;> ring
  simp only [velPhys, B0412.realC_apply, Nv, Axi.frameL_apply, hperG, inv_inv]
  rw [hDr', hDz']
  exact congrArg (fun r : ℝ => (r : ℂ)) (hvec _ _ i)

end UnforcedLeray.Short.PartIIIb.NearInst
