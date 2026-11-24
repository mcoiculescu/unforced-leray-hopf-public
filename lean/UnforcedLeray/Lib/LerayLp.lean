import UnforcedLeray.Lib.LerayLp.Transfer
import UnforcedLeray.Lib.LerayLp.RieszCZ
import UnforcedLeray.Lib.LerayLp.RieszLp
import UnforcedLeray.Lib.LerayLp.Leray
import UnforcedLeray.Lib.LerayLp.Duality
import UnforcedLeray.Lib.LerayLp.Cutoff
import UnforcedLeray.Lib.LerayLp.Helmholtz

/-!
# The Leray projection on `L^p(R³; R³)`, `1 < p < ∞` (Wave 2, block 2B LERAY-P: INF01 T13–T15)

Main file of block 2B of the Lean build plan

`𝔓 := Id + ∂∂(N ∗ ·)` on `L^p`, identified with the compiled `Leray.projection` at `p = 2`).
Targets and proposed signatures: `scoping/INF01-CZ.md` §5, Level 2 (T13–T15) and §4.2, §4.8.
Built on `Lib/CZCore` (the anisotropic Calderón–Zygmund theorem, T6–T12) and `Lib/CZL2` (the
`L²` Newton–Hessian operators, T1–T5). Namespace `UnforcedLeray.RieszLp`.

Manuscript: `R_j = ∂_j(-Δ)^{-1/2}`, `R_iR_k = ∂_i∂_k(-Δ)^{-1}` and the Leray projection
`𝔓 = I + R ⊗ R` (`paper/main.tex` lines 107–111, 3051); blueprint units B0414 (lines 7336–7344:
`P_σ` bounded on `L^q`, `1 < q < ∞`, orthogonal at `q = 2`, citing Grafakos Cor. 5.2.8),
B0430 (lines 3720–3732: consistency across exponents), B0439 (lines 7364–7387: `g = P_σ g` on
solenoidal fields) and B0797 (eq:ward:W2.6, lines 11539–11560: the Helmholtz complement of a
solenoidal `L^{p_0}` field vanishes, `(I − P)∇p_lift = ∇p_lift`). Real fields only; the `ℂ³`
version and the commutations (T16, T17) are later targets.

| Target | Module | Main declarations |
|---|---|---|
| T13 | `Transfer`, `RieszCZ`, `RieszLp` | `rieszFin`, `rieszKernelFin`, `hormander_rieszKernelFin`, `rieszFin_offSupport`, `integral_rieszFin_mul`, `rieszFin_isCZConvolution`, `rieszPairLp`, `rieszPairLp_toLp_ae`, `rieszPairLp_ae_of_memLp_two`, `rieszPairLp_two`, `rieszPairLp_consistent` |
| T14 | `Leray`, `Duality` | `lerayLp`, `coeFn_lerayLp`, `norm_lerayLp_le`, `eLpNorm_lerayLp_toLp_le`, `lerayLp_two`, `lerayLp_consistent`, `lerayLp_toLp_ae_eq_projection`, `lerayLp_ae_eq_projection`, `integral_inner_lerayLp_of_memLp_two`, `integral_inner_lerayLp_symm` |
| T15 | `Cutoff`, `Helmholtz` | `integral_inner_gradField_eq_zero`, `lerayLp_isSolenoidal`, `lerayLp_eq_self`, `lerayLp_idem`, `lerayLp_gradient_eq_zero` |

Deviations from the indicative signatures of `INF01-CZ.md` §5:

* T13: the Calderón–Zygmund core is stated on `Fin N → ℝ`, so the operator is transported along
  the volume-preserving coordinate map `toLp 2 : (Fin 3 → ℝ) → Space`
  (`rieszFin i k = toFinLp ∘ rieszPairL2 i k ∘ ofFinLp`, kernel `K_ik ∘ toLp`, isotropic weight
  `(1,1,1)` whose gauge is the sup norm). The Hörmander condition over sup-norm balls follows
  from the smoothness bound for `8|y| < 7|x|` (`abs_newtonHessianKernel_sub_le_of_lt`).
* `rieszPairLp`, `lerayLp` take `[Fact (1 ≤ p)]` (normed structure of `Lp`) and the hypotheses
  `1 < p`, `p ≠ ∞`.
* `norm_lerayLp_le : ∃ C, ∀ F, ‖𝔓F‖ ≤ C ‖F‖`; the constant depends on `p` only because
  `lerayLp` does. Its content is that `lerayLp p` is a bounded operator agreeing with the
  orthogonal projection on `L² ∩ L^p` (`lerayLp_ae_eq_projection`).
* `integral_inner_lerayLp_symm` takes any Hölder conjugate pair `(p, q)` with `1 < p, q < ∞`.
* `lerayLp_gradient_eq_zero` is the decaying case of §4.8: `φ` smooth with `φ ∈ L^r` for some
  `r ≥ 1` (`r = ∞` allowed) and `∇φ ∈ L^p`. The general Liouville form (`∇φ ∈ L^p` alone) is
  not proved; the note §4.8 records that only the decaying case is used.

Status: these are drafts. They do not prove Theorem A or `UnforcedLeray.MainClaim`.
-/
