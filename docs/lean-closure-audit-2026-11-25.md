# Audit de clôture Lean — 25 novembre 2026

Révision examinée : `e4e30232cef2b144291dde4c2008f9d5e9bb5ddf`.

**Conclusion : le projet compile et les résultats formels contrôlés sont valides dans Lean, mais la preuve de Goldbach reste conditionnelle. Le nouveau commit ne fournit aucune exclusion supplémentaire.** Il précise la force d'une estimation analytique encore à démontrer. Même une preuve de cette estimation sur sa bande actuelle ne suffirait pas à clôturer les deux murs.

Cet audit combine une lecture du code et des notes, trois relectures ciblées indépendantes et les vérifications ci-dessous. Il ne constitue pas une vérification intégrale de toutes les preuves analytiques citées. Aucun nouveau théorème Lean n'a été ajouté ou compilé pendant cet audit.

## Vérifications effectuées

- [GitHub Actions, exécution 45538232974](https://github.com/paulbado/Goldbachproof/actions/runs/45538232974), au commit audité : **succès**. Les journaux confirment `Build completed successfully (18268 jobs)`.
- Les 34 sorties `#print axioms` examinées utilisent uniquement des sous-ensembles de `propext`, `Classical.choice`, `Quot.sound`. Cela inclut `goldbach_of_walls`. Aucun `sorryAx` dans ces listes.
- Inspection statique des huit modules construits : aucun `sorry`, `admit`, nouvel `axiom`, `unsafe` ou `native_decide` détecté.
- Job Python de la même exécution : rangs premiers jusqu'à **199**, **2 960 556** candidats, **0** survivant. Le résultat jusqu'à 271 est annoncé par le dépôt ; il n'a pas été réexécuté ici.
- Exécution locale de `python scripts/distribution_profile.py` : résultats reproduits ci-dessous.
- Lean/Lake ne sont pas disponibles sur le PATH local ; la preuve de compilation utilisée ici est celle de la CI du commit exact, dont les journaux ont été consultés.

## Les obligations exactes du théorème final

Dans `Goldbach/WilliamsonMurIIBridge.lean:118`, `goldbach_of_walls` demande :

```lean
(P₀ : ℕ)
(hI : WallIAt P₀)
(hII : WallIIAt P₀)
(hsmall : ∀ P N, Nat.Prime P → 5 ≤ P → P < P₀ → ¬ BadFamily P N)
```

Il conclut `∀ N, 8 ≤ N → Even N → GoldbachAt N`. Les cas 4 et 6 seraient à raccorder à une formulation usuelle de Goldbach ; `GoldbachAt` exige actuellement deux nombres premiers au moins égaux à 3 (`WilliamsonMurIIBridge.lean:17`).

| Obligation | État au commit audité | Travail nécessaire |
|---|---|---|
| `WallIAt P₀` | Définition, pas de preuve (`WilliamsonMurII.lean:98`) | Exclure les familles avec une seule ligne déficiente, sous les conditions du rang précédent |
| `WallIIAt P₀` | Définition, pas de preuve (`WilliamsonMurII.lean:91`) | Exclure les familles avec au moins deux lignes déficientes, sur toutes les hauteurs pertinentes |
| `hsmall` | Pas de théorème raccordant les calculs Python | Certifier les petits rangs pour toutes les hauteurs, avec un seuil adapté aux murs |

L'ancienne vacuité liée à `BadFamily 3 4` est explicitement traitée. La définition actuelle de `FirstFailure` contient la garde `6 ≤ N` ; aucune nouvelle vacuité n'a été repérée dans la réduction.

## Ce que le nouveau commit apporte réellement

En posant `K = log N / log P`, le lemme T fournit une majoration de la forme

\[
\Sigma_{\mathrm{large}}(N)\le (K-\tfrac12+o(1))P.
\]

Pour obtenir la contradiction recherchée, il faut économiser une quantité fixe `ηP`, avec `η > 0`. La proposition PF exprime une condition suffisante sur un profil de distribution :

\[
\mathcal C(\lambda)=2\int_{1/2}^1\frac{d\theta}{\lambda(\theta)}
\le K-\tfrac12-\eta.
\]

Cette condition, ainsi que l'estimation des restes qui l'accompagne, n'est pas démontrée pour un profil admissible.

| Calcul reproduit | Valeur |
|---|---:|
| Profil calculé à partir des estimations disponibles dans la note | 11,5903025652 |
| Profil hypothétique combiné du script | 7,3676032645 |
| Seuil utile lorsque `5/3 ≤ K < 2` | de 1,166666… à moins de 1,5 |

Ces calculs ne sont pas des preuves d'estimations de distribution. Ils confirment que les profils envisagés ne donnent pas la marge nécessaire.

**Portée à préserver.** Ω ne concerne que `P^(5/3) ≤ N ≤ P^(2−ε)`, avec `ε > 0` fixé (`docs/residual-region.md:511`). Theorem W annonce seulement une borne `N < P^959` pour les grands rangs (`docs/theorem-W-dependencies.md:230`), améliorée à `P^950` dans une autre note. Il ne prouve pas l'absence de familles dans le domaine restant. Les autres bandes, le voisinage de `P²` et le raccord aux deux murs ne sont pas fermés par Ω.

## Corrections à effectuer avant de formaliser la nouvelle note

1. **Critère signé insuffisamment justifié — priorité mathématique.** `docs/distribution-profile.md:166` et `:190` proposent de déduire le contrôle SG des seules sommes de Kloosterman pondérées par `ρ_e`. Or, en écrivant `ψ = ψ_H + R_H` avec `|R_H| ≤ Δ_H`, l'erreur est majorée par

   \[
   \sum_e |\rho_e|\sum_q (\log q)\,\Delta_H(x_{e,q}).
   \]

   Choisir `H = P^λ (log P)^5` contrôle le terme constant du majorant, mais ne contrôle pas automatiquement ses termes de Fourier pondérés par `|ρ_e|`. Ceux-ci apparaissent explicitement dans `docs/hypothesis-T.md:267`. Il faut ajouter leur contrôle, traiter les points entiers aux extrémités, ou donner une autre dérivation complète. **PF formulé directement sous l'hypothèse SG exacte n'est pas invalidé par ce constat.**

2. **Mauvais profil dans le tableau.** À `docs/distribution-profile.md:144`, le profil affiché est `max(1−θ, min(2(1−θ), θ/2))`. Il vaut `2(1−θ)` pour `θ` assez proche de 1 : son intégrale diverge. La valeur 7,37 provient du troisième terme ajouté dans `scripts/distribution_profile.py:11`, qui doit être affiché dans le tableau.

3. **Conditions suffisantes présentées comme nécessaires.** Les lignes 129–131 de `docs/distribution-profile.md` extrapolent les familles numériques testées en une nécessité à chaque échelle, puis en une nécessité d'atteindre le niveau 1. Contre-exemple à cette lecture : `λ ≡ 0,9` donne `C = 10/9 < 7/6`, sans jamais atteindre 1. Cela ne prouve pas que ce profil est disponible ; cela réfute seulement la nécessité annoncée. Les seuils du tableau doivent rester rattachés aux familles de profils étudiées.

4. **Support de WF à préciser.** `r_e` est défini pour `e` impair sans carré, mais les produits `d₁d₂` de la formulation WF ne le sont pas nécessairement (`distribution-profile.md:46`, `:51`, `:59`). Restreindre les supports et imposer les conditions de coprimalité nécessaires, ou étendre explicitement la définition des restes et adapter l'implication S ⇒ WF.

5. **Inverse modulo `e` à définir sur le support réel.** Dans les sommes Selberg, écrire le support de `ρ_e`. Puisque `e = lcm(d₁,d₂)` et `d_j < D_i ≤ √P < q`, aucun `q` du bloc ne divise `e` sur ce support. L'inverse de `q` modulo `e` y est donc licite ; la somme ne doit pas laisser cette justification implicite.

6. **Comparaison fausse dans la note résiduelle.** `docs/residual-region.md:537` écrit `N ≥ P^(5/3) ≫ q²`. Pour `q` de taille `P` et `K < 2` fixé, on a au contraire `N/q² → 0`. Cette phrase doit être corrigée sans en déduire pour autant qu'une estimation externe s'applique.

Ces constats portent sur les notes analytiques. Ils ne changent pas le statut des théorèmes Lean déjà compilés.

## Étape formelle concrète : rendre les petits rangs certifiables

Une conséquence élémentaire des lemmes existants donne une borne finie pour **toute** famille mauvaise de rang premier `P ≥ 3` :

\[
N\le P+\operatorname{deficitBudget}(P,1).
\]

La déduction est la suivante :

1. `one_add_absent_le_deficient` (`WilliamsonMurIIClosure.lean:69`) implique qu'il existe une ligne déficiente.
2. Appliquer `deficit_height_bound` (`WilliamsonMurIIKLines.lean:194`) au singleton de cette ligne.
3. On obtient `N−P ≤ deficitBudget P 1` ; `BadFamily` donne `P<N`, d'où la borne annoncée.

Cette conséquence n'a pas été ajoutée comme théorème Lean dans cet audit. Elle fournit un premier objectif précis, sans nouvel apport analytique. Elle permettrait de remplacer le quantificateur non borné sur `N` de `hsmall` par une vérification finie. La borne est trop grande pour constituer à elle seule une stratégie de calcul efficace.

Pour réutiliser le script existant de manière plus efficace, il faut certifier la complétude de l'énumération des compléments déficients et la validité de chaque témoin premier d'élimination. Le script filtre `PreviousRankConditions` (`scripts/check_small_ranks.py:35`) : le raccord à `hsmall` nécessite donc une induction sur les rangs ou un raisonnement par premier échec. Le résultat Python seul ne peut pas remplir cet argument Lean.

Ordre de travail recommandé : formaliser la borne finie ci-dessus ; construire un vérificateur de certificats pour les premiers rangs ; raccorder ces certificats à une réduction par premier échec ; corriger les notes avant d'entreprendre la formalisation des estimations analytiques. Les murs doivent rester des hypothèses explicites tant que leurs preuves ne sont pas disponibles.

## Seuils et limites de la voie analytique

Theorem W annonce un seuil effectif mais non calculé. La valeur indicative `log P ≳ 2,3 × 10^23` n'est pas un seuil intégralement explicité et certifié (`theorem-W-dependencies.md:248` et `:291`). La voie Ω utilise en outre une version de Bombieri–Vinogradov annoncée comme ineffective dans le dépôt (`residual-region.md:516`). Le contrôle jusqu'à 199 ou 271 ne raccorde donc pas les preuves asymptotiques actuelles.

Une piste bibliographique récente mérite une étude séparée : Daniel R. Johnston, [An effective Bombieri–Vinogradov error term for sifting problems, version 3, août 2026](https://arxiv.org/abs/2510.10853v3). Cet article annonce une méthode d'effectivisation pour les problèmes classiques de crible. Son applicabilité aux sommes et uniformités exactes de ce dépôt n'a pas été vérifiée ici ; il ne fournit pas à lui seul l'estimation Ω manquante.

**Critère de clôture :** disposer de preuves de `WallIAt P₀`, `WallIIAt P₀` et `hsmall` pour un même seuil, puis les appliquer effectivement à `goldbach_of_walls` et contrôler les axiomes du théorème résultant. La compilation actuelle valide la réduction conditionnelle ; ces trois arguments restent à construire.
