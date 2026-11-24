import UnforcedLeray.Short.PartIIIb.Concrete.ReturnInst.AffineSource.RADefs

/-!
# `PartIII-b:C/asrc/ra/9` : `RAGeoBound` from the four ring-chart pieces (source 5034-5044)

Source of record: `the November 2 reference manuscript` (73 pages).

The geometric remainder `geoCoef = rAcoef(U_raw) - s·r_per` (`RADefs.lean`) is, by linearity of
`coefOf` and of `toMer`, exactly the sum of the four differences between the chart coefficient of
one term of `𝔯_A = D_μĥ_A + div(U⊗ĥ_A + ĥ_A⊗U) - F_A - E_A - ∇_y(sΨ_A)` on `U_raw` and the
corresponding Cartesian term of `r_per` (source 5023-5028, `s·` the chart weight):

* `geoDPiece` : `D_μ ĥ_A` against `(∂_s + μ/s - νΔ_{q,η})h^p_A` -- the ring-chart rules
  `∂_r = √s(∂_q - ε𝒦)`, `∂_z = √s∂_η`, `(∂_τ - y·∇/2 - 1/2)(√s b) = s^{3/2}∂_s b`, the physical
  Laplacian `s^{3/2}[(Δ_{q,η} - 2ε(𝒦+1)∂_q + ε²(𝒦+1)²)b - ε²b_re_r]` and the stream completion
  `ε(1-𝒦)ψ^p_A` of `ĥ_A` (source 5034-5039, 4979-4980);
* `geoConvPiece` : `div(U_raw⊗ĥ_A + ĥ_A⊗U_raw)` against `(v·∇)h^p_A + (h^p_A·∇)v` -- the chart rules
  for the divergence, `1/r = ε√s`, and the stream completion `εH` of `U_raw = p.raw`
  (source 5040-5044, 2076-2077);
* `geoFEPiece` : `F_A + E_A` against `f_A + e_A` (the lift of `FAcoef + EAcoef = s(f_A + e_A)`,
  source 4981);
* `geoGradPiece` : `∇_y(sΨ_A)` against `∇_{q,η}Ψ_A` -- the pressure completion
  `s^{3/2}∇_{q,η}Ψ_A = ∇_y(sΨ_A) + εs^{3/2}(𝒦+2)Ψ_Ae_r` (source 5039-5043).

Each piece satisfies the bound of `RAGeoBound` (`RAGeoPieceBound`, with in addition the measurability
of the cell sections, needed to add the cell integrals).  The bounds of the four pieces are the
leaves (`RAGeoDLeaf`, `RAGeoConvLeaf`, `RAGeoFELeaf`, `RAGeoGradLeaf`); `raGeoBound_of` assembles them.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter UnforcedLeray.Axi
open scoped ENNReal

namespace UnforcedLeray.Short.PartIIIb.Concrete

open UnforcedLeray.PhaseSpace UnforcedLeray.B0411
open UnforcedLeray.Cons.C03.Concrete (pairF phaseInt IsSolTest Params)
open UnforcedLeray.Blueprint.Planar (PlanarData)

/-! ## 1. The four pieces -/

theorem toMer_add (a b : ℝ × ℝ) : toMer (a + b) = toMer a + toMer b := by
  ext i; fin_cases i <;> simp [toMer]

theorem toMer_sub (a b : ℝ × ℝ) : toMer (a - b) = toMer a - toMer b := by
  ext i; fin_cases i <;> simp [toMer]

theorem toMer_smul (r : ℝ) (a : ℝ × ℝ) : toMer (r • a) = r • toMer a := by
  ext i; fin_cases i <;> simp [toMer]

/-- `D_μĥ_A` on the chart against `s(∂_s + μ/s - νΔ_{q,η})h^p_A` (source 5034-5039). -/
def geoDPiece (p : Params) (μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : Chart → Merid :=
  coefOf p.ε⁻¹ (physDmu p.ν μ (hLift p.ν p.ε p.c χf A)) -
    fun q => q.1 • toMer (deriv (fun s' => hpA p.ν χf A s' q.2) q.1 +
      (μ / q.1) • hpA p.ν χf A q.1 q.2 - p.ν • lapPl (hpA p.ν χf A q.1) q.2)

/-- `div(U_raw⊗ĥ_A + ĥ_A⊗U_raw)` on the chart against `s((v·∇)h^p_A + (h^p_A·∇)v)`
(source 5040-5044). -/
def geoConvPiece (p : Params) (_μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : Chart → Merid :=
  coefOf p.ε⁻¹ (fun τ y => physDivSym (p.raw τ) (hLift p.ν p.ε p.c χf A τ) y) -
    fun q => q.1 • toMer (fderiv ℝ (hpA p.ν χf A q.1) q.2 (trainPl p.train q.1 q.2) +
      fderiv ℝ (trainPl p.train q.1) q.2 (hpA p.ν χf A q.1 q.2))

/-- `F_A + E_A` on the chart against `s(f_A + e_A)` (source 4981). -/
def geoFEPiece (p : Params) (μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : Chart → Merid :=
  coefOf p.ε⁻¹ (feLift p.ν μ p.ε p.c χf A) -
    fun q => q.1 • toMer (merPl (fA p.ν μ χf A q.1 q.2) + merPl (eA p.ν μ χf A q.1 q.2))

/-- `∇_y(sΨ_A)` on the chart against `s∇_{q,η}Ψ_A` (source 5039-5043). -/
def geoGradPiece (p : Params) (_μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) : Chart → Merid :=
  coefOf p.ε⁻¹ (fun τ y => physGrad (psiLift p.ν p.ε χf A τ) y) -
    fun q => q.1 • toMer (mgrad (PsiA p.ν χf A q.1) q.2)

theorem coefOf_comb (R : ℝ) (a b c d : ℝ → Space → Space) (q : Chart) :
    coefOf R (fun τ y => a τ y + b τ y - c τ y - d τ y) q =
      coefOf R a q + coefOf R b q - coefOf R c q - coefOf R d q := by
  unfold coefOf
  ext i
  fin_cases i <;> simp <;> ring

/-- **The decomposition** `geoCoef = D + Conv - FE - Grad` (linearity of `coefOf`, `toMer`). -/
theorem geoCoef_eq (p : Params) (μ : ℝ) (χf : ℝ → ℝ) (A : ℝ → Mat3) :
    geoCoef p μ χf A =
      geoDPiece p μ χf A + geoConvPiece p μ χf A - geoFEPiece p μ χf A -
        geoGradPiece p μ χf A := by
  funext q
  have h1 : rAcoef p.ν μ p.ε p.c χf p.raw A q =
      coefOf p.ε⁻¹ (physDmu p.ν μ (hLift p.ν p.ε p.c χf A)) q +
        coefOf p.ε⁻¹ (fun τ y => physDivSym (p.raw τ) (hLift p.ν p.ε p.c χf A τ) y) q -
        coefOf p.ε⁻¹ (feLift p.ν μ p.ε p.c χf A) q -
        coefOf p.ε⁻¹ (fun τ y => physGrad (psiLift p.ν p.ε χf A τ) y) q :=
    coefOf_comb p.ε⁻¹ _ _ _ _ q
  have h2 : rPerCoef μ χf p.train A q = q.1 • toMer (rPer μ χf p.train A q.1 q.2) := rfl
  unfold geoCoef
  rw [Pi.sub_apply, h1, h2]
  unfold rPer
  simp only [Pi.sub_apply, Pi.add_apply, geoDPiece, geoConvPiece, geoFEPiece, geoGradPiece,
    toMer_add, toMer_sub, toMer_smul, smul_add, smul_sub]
  abel

/-! ## 2. The bound of a piece -/

/-- **`RAGeoBound` for a family `g` of chart coefficients** (the conclusion of `RAGeoBound`, with
`geoCoef p μ χf A` replaced by `g p μ A`), together with the a.e. strong measurability of the cell
sections `x ↦ g(s, x)` (needed to add the cell integrals). -/
def RAGeoPieceBound (as : ℝ) (χf : ℝ → ℝ) (g : Params → ℝ → (ℝ → Mat3) → Chart → Merid) : Prop :=
  IsSourceCutoffC χf → ∀ K : Set ℝ, IsCompact K → K ⊆ Ioo 0 (1 / 4) → ∀ dm dp : ℝ, 0 < dm →
    ∃ (C : ℝ) (k : ℕ) (ν₀ : ℝ), 0 < ν₀ ∧
      ∀ (p : Params) (d : ℝ), UnforcedLeray.Short.IIb.BgRegime p d dm dp → p.ν ≤ ν₀ →
      ∀ μ ∈ K, ∀ A : ℝ → Mat3, IsAffElem as A →
        AEStronglyMeasurable (g p μ A) (srcMeasure p.c) ∧
        (∀ s : ℝ, (11 / 10) / p.ν < s → ∀ x : ℝ × ℝ, g p μ A (s, x) = 0) ∧
        (∀ s : ℝ, 0 < s →
          AEStronglyMeasurable (fun x : ℝ × ℝ => g p μ A (s, x)) (UnforcedLeray.Cyl.avgμ p.c)) ∧
        ∀ s : ℝ, 0 < s → s ≤ (11 / 10) / p.ν →
          ∫⁻ x, ENNReal.ofReal (‖g p μ A (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ p.c)
            ≤ ENNReal.ofReal ((C * p.ν⁻¹ ^ k * p.ε * affM p.ν χf A *
                (s ^ (5 / 2 : ℝ) + s ^ (7 / 2 : ℝ))) ^ 2)

theorem RAGeoPieceBound.neg {as : ℝ} {χf : ℝ → ℝ} {g : Params → ℝ → (ℝ → Mat3) → Chart → Merid}
    (h : RAGeoPieceBound as χf g) :
    RAGeoPieceBound as χf (fun p μ A q => -g p μ A q) := by
  intro hχ K hK hKs dm dp hdm
  obtain ⟨C, k, ν₀, hν₀, H⟩ := h hχ K hK hKs dm dp hdm
  refine ⟨C, k, ν₀, hν₀, fun p d hreg hν μ hμ A hA => ?_⟩
  obtain ⟨m, z, sm, b⟩ := H p d hreg hν μ hμ A hA
  refine ⟨m.neg, fun s hs x => by simp [z s hs x], fun s hs => (sm s hs).neg, fun s hs hsT => ?_⟩
  simpa using b s hs hsT

theorem RAGeoPieceBound.add {as : ℝ} {χf : ℝ → ℝ}
    {g₁ g₂ : Params → ℝ → (ℝ → Mat3) → Chart → Merid}
    (h₁ : RAGeoPieceBound as χf g₁) (h₂ : RAGeoPieceBound as χf g₂) :
    RAGeoPieceBound as χf (fun p μ A q => g₁ p μ A q + g₂ p μ A q) := by
  intro hχ K hK hKs dm dp hdm
  obtain ⟨C₁, k₁, n₁, hn₁, H₁⟩ := h₁ hχ K hK hKs dm dp hdm
  obtain ⟨C₂, k₂, n₂, hn₂, H₂⟩ := h₂ hχ K hK hKs dm dp hdm
  refine ⟨2 * (|C₁| + |C₂|), max k₁ k₂, min (min n₁ n₂) 1, by positivity,
    fun p d hreg hν μ hμ A hA => ?_⟩
  have hν₁ : p.ν ≤ n₁ := hν.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hν₂ : p.ν ≤ n₂ := hν.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hν1 : p.ν ≤ 1 := hν.trans (min_le_right _ _)
  have hν0 : 0 < p.ν := p.ν_pos
  obtain ⟨m₁, z₁, s₁, b₁⟩ := H₁ p d hreg hν₁ μ hμ A hA
  obtain ⟨m₂, z₂, s₂, b₂⟩ := H₂ p d hreg hν₂ μ hμ A hA
  refine ⟨m₁.add m₂, fun s hs x => by simp [z₁ s hs x, z₂ s hs x],
    fun s hs => (s₁ s hs).add (s₂ s hs), fun s hs hsT => ?_⟩
  have hb₁ := b₁ s hs hsT
  have hb₂ := b₂ s hs hsT
  obtain ⟨F, hF⟩ : ∃ F : ℝ, F = p.ε * affM p.ν χf A * (s ^ (5 / 2 : ℝ) + s ^ (7 / 2 : ℝ)) :=
    ⟨_, rfl⟩
  have hb₁' : ∫⁻ x, ENNReal.ofReal (‖g₁ p μ A (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ p.c) ≤
      ENNReal.ofReal ((C₁ * p.ν⁻¹ ^ k₁ * F) ^ 2) := by
    have e : C₁ * p.ν⁻¹ ^ k₁ * F = C₁ * p.ν⁻¹ ^ k₁ * p.ε * affM p.ν χf A *
        (s ^ (5 / 2 : ℝ) + s ^ (7 / 2 : ℝ)) := by rw [hF]; ring
    rw [e]; exact hb₁
  have hb₂' : ∫⁻ x, ENNReal.ofReal (‖g₂ p μ A (s, x)‖ ^ 2) ∂(UnforcedLeray.Cyl.avgμ p.c) ≤
      ENNReal.ofReal ((C₂ * p.ν⁻¹ ^ k₂ * F) ^ 2) := by
    have e : C₂ * p.ν⁻¹ ^ k₂ * F = C₂ * p.ν⁻¹ ^ k₂ * p.ε * affM p.ν χf A *
        (s ^ (5 / 2 : ℝ) + s ^ (7 / 2 : ℝ)) := by rw [hF]; ring
    rw [e]; exact hb₂
  have hmeas : ∀ (g : Chart → Merid), AEStronglyMeasurable (fun x : ℝ × ℝ => g (s, x))
      (UnforcedLeray.Cyl.avgμ p.c) →
      AEMeasurable (fun x : ℝ × ℝ => ENNReal.ofReal (‖g (s, x)‖ ^ 2))
        (UnforcedLeray.Cyl.avgμ p.c) := fun g hg =>
    (hg.norm.aemeasurable.pow_const 2).ennreal_ofReal
  have hpt : ∀ x : ℝ × ℝ,
      ENNReal.ofReal (‖g₁ p μ A (s, x) + g₂ p μ A (s, x)‖ ^ 2) ≤
        ENNReal.ofReal 2 * ENNReal.ofReal (‖g₁ p μ A (s, x)‖ ^ 2) +
          ENNReal.ofReal 2 * ENNReal.ofReal (‖g₂ p μ A (s, x)‖ ^ 2) := by
    intro x
    rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
      ← ENNReal.ofReal_add (by positivity) (by positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    have := norm_add_le (g₁ p μ A (s, x)) (g₂ p μ A (s, x))
    nlinarith [norm_nonneg (g₁ p μ A (s, x)), norm_nonneg (g₂ p μ A (s, x)),
      norm_nonneg (g₁ p μ A (s, x) + g₂ p μ A (s, x)),
      sq_nonneg (‖g₁ p μ A (s, x)‖ - ‖g₂ p μ A (s, x)‖)]
  calc ∫⁻ x, ENNReal.ofReal (‖g₁ p μ A (s, x) + g₂ p μ A (s, x)‖ ^ 2)
          ∂(UnforcedLeray.Cyl.avgμ p.c)
      ≤ ∫⁻ x, (ENNReal.ofReal 2 * ENNReal.ofReal (‖g₁ p μ A (s, x)‖ ^ 2) +
          ENNReal.ofReal 2 * ENNReal.ofReal (‖g₂ p μ A (s, x)‖ ^ 2))
          ∂(UnforcedLeray.Cyl.avgμ p.c) := lintegral_mono hpt
    _ = ENNReal.ofReal 2 * ∫⁻ x, ENNReal.ofReal (‖g₁ p μ A (s, x)‖ ^ 2)
          ∂(UnforcedLeray.Cyl.avgμ p.c) +
        ENNReal.ofReal 2 * ∫⁻ x, ENNReal.ofReal (‖g₂ p μ A (s, x)‖ ^ 2)
          ∂(UnforcedLeray.Cyl.avgμ p.c) := by
        rw [lintegral_add_left' ((hmeas _ (s₁ s hs)).const_mul _),
          lintegral_const_mul'' _ (hmeas _ (s₁ s hs)),
          lintegral_const_mul'' _ (hmeas _ (s₂ s hs))]
    _ ≤ ENNReal.ofReal 2 * ENNReal.ofReal ((C₁ * p.ν⁻¹ ^ k₁ * F) ^ 2) +
        ENNReal.ofReal 2 * ENNReal.ofReal ((C₂ * p.ν⁻¹ ^ k₂ * F) ^ 2) := by
        gcongr
    _ = ENNReal.ofReal (2 * (C₁ * p.ν⁻¹ ^ k₁ * F) ^ 2 + 2 * (C₂ * p.ν⁻¹ ^ k₂ * F) ^ 2) := by
        rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal ((2 * (|C₁| + |C₂|) * p.ν⁻¹ ^ max k₁ k₂ * F) ^ 2) := by
        refine ENNReal.ofReal_le_ofReal ?_
        have hi : (1 : ℝ) ≤ p.ν⁻¹ := one_le_inv_iff₀.2 ⟨hν0, hν1⟩
        have e1 : p.ν⁻¹ ^ k₁ ≤ p.ν⁻¹ ^ max k₁ k₂ := pow_le_pow_right₀ hi (le_max_left _ _)
        have e2 : p.ν⁻¹ ^ k₂ ≤ p.ν⁻¹ ^ max k₁ k₂ := pow_le_pow_right₀ hi (le_max_right _ _)
        have a1 : 0 ≤ p.ν⁻¹ ^ k₁ := by positivity
        have a2 : 0 ≤ p.ν⁻¹ ^ k₂ := by positivity
        set a := p.ν⁻¹ ^ max k₁ k₂
        have x1 : |C₁ * p.ν⁻¹ ^ k₁| ≤ |C₁| * a := by
          rw [abs_mul, abs_of_nonneg a1]; exact mul_le_mul_of_nonneg_left e1 (abs_nonneg _)
        have x2 : |C₂ * p.ν⁻¹ ^ k₂| ≤ |C₂| * a := by
          rw [abs_mul, abs_of_nonneg a2]; exact mul_le_mul_of_nonneg_left e2 (abs_nonneg _)
        have y1 : (C₁ * p.ν⁻¹ ^ k₁) ^ 2 ≤ (|C₁| * a) ^ 2 := by
          rw [← sq_abs (C₁ * p.ν⁻¹ ^ k₁)]; exact pow_le_pow_left₀ (abs_nonneg _) x1 2
        have y2 : (C₂ * p.ν⁻¹ ^ k₂) ^ 2 ≤ (|C₂| * a) ^ 2 := by
          rw [← sq_abs (C₂ * p.ν⁻¹ ^ k₂)]; exact pow_le_pow_left₀ (abs_nonneg _) x2 2
        have hF2 : 0 ≤ F ^ 2 := sq_nonneg F
        have z1 := mul_le_mul_of_nonneg_right y1 hF2
        have z2 := mul_le_mul_of_nonneg_right y2 hF2
        have hc : 0 ≤ |C₁| * a := by positivity
        have hc2 : 0 ≤ |C₂| * a := by positivity
        have hcc : (|C₁| * a) ^ 2 + (|C₂| * a) ^ 2 ≤ (|C₁| * a + |C₂| * a) ^ 2 := by
          nlinarith [mul_nonneg hc hc2]
        have hcc2 := mul_le_mul_of_nonneg_right hcc hF2
        calc 2 * (C₁ * p.ν⁻¹ ^ k₁ * F) ^ 2 + 2 * (C₂ * p.ν⁻¹ ^ k₂ * F) ^ 2
            = 2 * ((C₁ * p.ν⁻¹ ^ k₁) ^ 2 * F ^ 2) + 2 * ((C₂ * p.ν⁻¹ ^ k₂) ^ 2 * F ^ 2) := by
              ring
          _ ≤ 2 * ((|C₁| * a) ^ 2 * F ^ 2) + 2 * ((|C₂| * a) ^ 2 * F ^ 2) := by linarith
          _ ≤ 4 * ((|C₁| * a + |C₂| * a) ^ 2 * F ^ 2) := by nlinarith
          _ = (2 * (|C₁| + |C₂|) * a * F) ^ 2 := by ring
    _ = _ := by congr 2; rw [hF]; ring

/-! ## 3. The leaves: the bounds of the four pieces (source 5034-5044) -/

/-- **Leaf D** (source 5034-5039, 4979-4980): the ring-chart rules for `D_μ` on the lift `ĥ_A`
(with its stream completion `ε(1-𝒦)ψ^p_A`) give `coefOf(D_μĥ_A) = s(∂_s + μ/s - νΔ_{q,η})h^p_A`
up to `ε s G`, `G` a finite sum of products of `(s∂_s)^iA^y` (`i ≤ 4`), Gaussian polynomials and
the lattice kernels, of normalized cell norm `≤ P_ν M(A)(s^{3/2}+s^{5/2})`. -/
def RAGeoDLeaf (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  RAGeoPieceBound as χf (fun p μ A => geoDPiece p μ χf A)

/-- **Leaf Conv** (source 5040-5044, 2076-2077): `div(U_raw⊗ĥ_A + ĥ_A⊗U_raw)` against
`s((v·∇)h^p_A + (h^p_A·∇)v)`, the difference is the `1/r = ε√s` terms and the `εH`, `ε` stream
completions of `U_raw` and `ĥ_A`. -/
def RAGeoConvLeaf (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  RAGeoPieceBound as χf (fun p μ A => geoConvPiece p μ χf A)

/-- **Leaf FE** (source 4981): `F_A + E_A` is the lift of `FAcoef + EAcoef = s(f_A + e_A)`; the
piece vanishes on the cell (periodic extension `perExt` is the identity there) and is `c`-periodic
and zero for `s > 1.1/ν`. -/
def RAGeoFELeaf (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  RAGeoPieceBound as χf (fun p μ A => geoFEPiece p μ χf A)

/-- **Leaf Grad** (source 5039-5043): the pressure completion
`s^{3/2}∇_{q,η}Ψ_A = ∇_y(sΨ_A) + εs^{3/2}(𝒦+2)Ψ_Ae_r`. -/
def RAGeoGradLeaf (as : ℝ) (χf : ℝ → ℝ) : Prop :=
  RAGeoPieceBound as χf (fun p μ A => geoGradPiece p μ χf A)

/-- **`RAGeoBound` from the four leaves.** -/
theorem raGeoBound_of (as : ℝ) (χf : ℝ → ℝ) (hD : RAGeoDLeaf as χf) (hC : RAGeoConvLeaf as χf)
    (hF : RAGeoFELeaf as χf) (hG : RAGeoGradLeaf as χf) : RAGeoBound as χf := by
  have h : RAGeoPieceBound as χf (fun p μ A => geoCoef p μ χf A) := by
    have e : (fun (p : Params) (μ : ℝ) (A : ℝ → Mat3) => geoCoef p μ χf A) =
        fun p μ A q => (geoDPiece p μ χf A q + geoConvPiece p μ χf A q) +
          -geoFEPiece p μ χf A q + -geoGradPiece p μ χf A q := by
      funext p μ A q
      rw [geoCoef_eq]
      simp only [Pi.sub_apply, Pi.add_apply]
      abel
    rw [e]
    exact ((hD.add hC).add hF.neg).add hG.neg
  intro hχ K hK hKs dm dp hdm
  obtain ⟨C, k, ν₀, hν₀, H⟩ := h hχ K hK hKs dm dp hdm
  refine ⟨C, k, ν₀, hν₀, fun p d hreg hν μ hμ A hA => ?_⟩
  obtain ⟨m, z, _, b⟩ := H p d hreg hν μ hμ A hA
  exact ⟨m, z, b⟩

end UnforcedLeray.Short.PartIIIb.Concrete
