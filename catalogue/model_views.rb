# Present all recorded models without changing mathematical registrations.
require 'json'
require 'cgi'
require 'digest'
module AtlasModelViews
  class View
    attr_reader :registry,:overlay,:contracts,:models,:comparisons
    def initialize(root)
      @root=root
      @registry=read_json('catalogue/catalogue.json')
      @overlay=read_json('catalogue/realizations.json')
      @contracts=read_json('verification/existence/registry.json').fetch('entries')
      @comparisons=overlay.fetch('comparisons').select { |c|c['proof_status']=='construction_complete' }
      @models={}
      registry.fetch('entries').each do |e|
        default=overlay.fetch('first_completed_anchors').find { |a|a['entry']==e['id'] } ||
          overlay.fetch('legacy_defaults').find { |a|a['entry']==e['id'] }
        id=default.fetch('realization')
        @models[e['id']]=[{'id'=>id,'label'=>model_label(id),'carrier'=>e.dig('roles','model'),
          'roles'=>e.fetch('roles'),'parameters'=>e.fetch('parameters'),'construction'=>e.fetch('construction'),
          'default'=>true,'status'=>'construction_complete','entry'=>e['id']}]
        overlay.fetch('candidates').select { |c|c['entry']==e['id'] && c['realization']!=id }.each do |c|
          contract=contracts.find { |r|r['catalogue_id']==e['id'] && r['realization']==c['realization'] }
          next unless c['proof_status']=='construction_complete' || contract
          if c['carrier']
            roles={'model'=>c['carrier']}.merge(c.fetch('property_evidence').transform_values { |p|p.fetch('theorem') })
          else
            # These two uniform models already have successful dated contracts;
            # their separate registry registration has not been completed.
            type=e.fetch('id').split('.').last
            raise 'Unsupported unregistered model' unless %w[G2 F4].include?(type) && contract
            solution=File.read(root+'/'+contract['evidence']+'/'+contract['solution_file'])
            raise 'Wrong concrete contract witness' unless solution.include?("Atlas.Chevalley.Model .#{type} F")
            roles={'model'=>{'declaration'=>'Atlas.Chevalley.Model .'+type,'source'=>'Atlas/LinearGroups/Chevalley/Models.lean'},
              'order'=>{'declaration'=>'Atlas.Chevalley.model_'+type+'_card','source'=>'Atlas/LinearGroups/Chevalley/Model'+type+'Order.lean'},
              'simple'=>{'declaration'=>'Atlas.Chevalley.model_isSimpleGroup_of_good','source'=>'Atlas/LinearGroups/Chevalley/ModelSimplicityGood.lean'}}
          end
          @models[e['id']]<<{'id'=>c['realization'],'label'=>model_label(c['realization']),'carrier'=>roles['model'],
            'roles'=>roles,'parameters'=>c['parameter_domain'],'construction'=>c['construction_meaning'],
            'default'=>false,'status'=>c['proof_status'],'entry'=>e['id'],'record'=>c,'contract'=>contract}
        end
      end
    end
    def read_json(p)=JSON.parse(File.read(@root+'/'+p))
    def model_label(id)
      {'matrix'=>'Projective special-linear matrix model','quadratic'=>'Quadratic-form model',
       'symplectic'=>'Symplectic matrix model','albert'=>'Split-Albert model','octonion'=>'Split-octonion model',
       'chevalley'=>'Chevalley root-operator model','legacy'=>'Original concrete model'}.fetch(id,id)
    end
    def short_label(model)
      labels={'matrix'=>'Matrix','quadratic'=>'Quadratic','symplectic'=>'Symplectic',
        'albert'=>'Albert','octonion'=>'Octonion','chevalley'=>'Chevalley'}
      return labels.fetch(model['id']) if labels.key?(model['id'])
      {'family.Cyclic'=>'Residues','family.Alternating'=>'Permutation','family.PSU'=>'Hermitian',
       'family.Suzuki'=>'Matrix','family.2D'=>'Quadratic','family.3D4'=>'Triality','family.ReeG2'=>'Matrix',
       'exceptional.Tits'=>'Lattice','sporadic.M11'=>'Golay','sporadic.M12'=>'Golay','sporadic.M22'=>'Golay',
       'sporadic.M23'=>'Golay','sporadic.M24'=>'Golay','sporadic.Co1'=>'Leech','sporadic.Co2'=>'Leech',
       'sporadic.Co3'=>'Leech','sporadic.McL'=>'Leech','sporadic.HS'=>'Leech','sporadic.Suz'=>'Eisenstein',
       'sporadic.J2'=>'Icosian','sporadic.Fi22'=>'Rays','sporadic.Fi23'=>'Rays','sporadic.Fi24Prime'=>'Rays',
       'sporadic.Ru'=>'Lattice'}.fetch(model.fetch('entry'))
    end
    def anchor(id)=id.downcase.tr('.','-')
    def model_anchor(m)=anchor(m['entry'])+'-'+m['id']
    def edges(id)=comparisons.select { |c|c.dig('source','qualified_id').split('/').first==id || c.dig('target','qualified_id').split('/').first==id }
    def multiple = models.select { |_id,ms|ms.size>1 }
    def link(ref,prefix='')
      path=ref.fetch('source')
      if path.start_with?('.lake/packages/mathlib/')
        rev=read_json('lake-manifest.json')['packages'].find { |p|p['name']=='mathlib' }.fetch('rev')
        return 'https://github.com/leanprover-community/mathlib4/blob/'+rev+'/'+path.delete_prefix('.lake/packages/mathlib/')
      end
      name=ref.fetch('declaration').split('.').last.split.first
      lines=File.readlines(@root+'/'+path)
      i=lines.index { |l|l.match?(/\b(?:def|theorem|abbrev|instance)\s+#{Regexp.escape(name)}(?:\s|\.|\{|\()/) }
      prefix+path+(i ? "#L#{i+1}" : '')
    end
    def source(ref,prefix='')="[`#{ref.fetch('declaration')}`](#{link(ref,prefix)})"
    def proof_source(ref)
      name=ref.fetch('declaration').split('.').last
      lines=File.readlines(@root+'/'+ref.fetch('source'))
      first=lines.index { |l|l.match?(/^def #{Regexp.escape(name)}\b/) } or raise 'Missing isomorphism definition'
      last=(first+1...lines.size).find { |i|lines[i].match?(%r{^(?:/--|def |theorem |instance |end )}) } || lines.size
      lines[first...last].join.rstrip
    end
    def certificate(c,prefix='')="[Lean isomorphism certificate](#{prefix}catalogue/ISOMORPHISMS.md##{c.fetch('id')})"
    def summary(id,prefix='')
      models.fetch(id).map { |m|"[#{short_label(m)}](#{prefix}CATALOGUE.md##{model_anchor(m)})" }.join(' · ')
    end
    def detailed(e,prefix='')
      ms=models.fetch(e['id']);text=""
      ms.each do |m|
        text+="<a id=\"#{model_anchor(m)}\"></a>\n\n### #{m['label']}\n\n#{m['construction']}\n\nParameters: #{m['parameters']}\n\n"
        text+="| Interface | Lean declaration and source |\n|---|---|\n"
        m['roles'].each do |role,ref|
          next if role=='nonabelian'
          text+="| #{role} | #{source(ref,prefix)} |\n"
        end
        text+="\n"
        if m['record'] && m['status']=='construction_complete'
          simple=m['record'].dig('property_evidence','simple')
          text+="Simplicity range: #{simple.dig('domain','description')}.\n\n"
          ev=m['record'].fetch('property_evidence')
          text+="Separate property audits: "+ev.reject { |k,_|k=='nonabelian' }.map { |k,v|"[#{k}](#{prefix}#{v.dig('binding','directory')})" }.join(' · ')+".\n\n"
        end
        if (r=m['contract'])
          p=r.fetch('evidence')
          text+="Dated concrete-model contract: [#{r['declaration']}](#{prefix}#{p}/#{r['solution_file']}) · [exact specification](#{prefix}#{p}/#{r['reference_file']}) · [checker receipt](#{prefix}#{p}/RESULT.json).\n\n"
          if m['status']!='construction_complete'
            range=e['id']=='family.G2' ? 'q > 2 for simplicity (the same model exists at q = 2)' : 'every finite field, q ≥ 2'
            text+="This contract proves order and simplicity of this explicit witness for #{range}. The realization registry still records its separate catalogue registration as pending.\n\n"
          end
        end
      end
      if ms.size>1
        text+="### Isomorphism between these constructions\n\n"
        if edges(e['id']).empty?
          text+=comparison_status(e['id'])+"\n\n"
        else
          edges(e['id']).each do |c|
            text+="#{source(c.fetch('witness'),prefix)} is the actual multiplicative equivalence.\n\n"
            text+="Domain: #{c.dig('parameter_domain','description')}.\n\n"
            text+="#{certificate(c,prefix)} gives the verbatim compiled type, both carriers, the parameter map and [full dependency audit](#{prefix}#{c.dig('evidence','directory')}).\n\n"
          end
        end
        text+="The existing order/simplicity dependency diagram and line counts describe the #{ms.first['label'].downcase}. They are not counts for both constructions combined.\n\n"
      end
      text
    end
    def comparison_status(id)
      case id
      when 'family.F4'
        'The isomorphism between the Chevalley and full split-Albert models remains unfinished. No certificate identifying them is claimed.'
      when 'family.G2'
        'The research note records a marked Chevalley–octonion equivalence with ten passed local audit scopes, but its final preservation/registration and source export are outside this review snapshot. This review therefore supplies both model contracts, without claiming that their isomorphism certificate is included.'
      else
        'No registered isomorphism certificate between these models is present in this snapshot.'
      end
    end
    def extra_statement_names
      models.values.flatten.reject { |m|m['default'] || m['status']!='construction_complete' }
        .flat_map { |m|%w[order simple].map { |r|m.dig('roles',r,'declaration') } }+
        comparisons.map { |c|c.dig('witness','declaration') }
    end
    def comparison_rows
      data=read_json('catalogue/comparisons.json')
      data.fetch('entries')+data.fetch('supplements').flat_map { |s|s.fetch('entries') }
    end
    def comparison_ref(id,title='certificate')
      row=comparison_rows.find { |r|r['id']==id } or raise "Unknown comparison #{id}"
      "[#{title}](#{link(row,'../')})"
    end
    def theorem_ref(name,path,title=name.split('.').last)
      "[#{title}](#{link({'declaration'=>name,'source'=>path},'../')})"
    end
    def comparison_guide
      main='Atlas/Comparisons.lean'
      arithmetic='Atlas/OrderArithmetic/Classification.lean'
      text=<<~MD
        # Constructions and identification certificates

        This page distinguishes three questions and links the Lean proofs answering
        them. Every identification is an actual group isomorphism between the stated
        models. The full construction inventory follows the comparison guide.

        | Question | Where to look |
        |---|---|
        | Do two constructions of the same group agree? | [Models of the same group](#same-group) |
        | Which different family labels describe isomorphic groups? | [Isomorphisms between families](#between-families) |
        | How are all remaining pairs distinguished? | [One general certificate, orders and invariants](#remaining-pairs) |

        **Coverage:** the general comparison theorem covers 13 families, all 16
        completed sporadic groups and Tits, on its exact simple parameter ranges.
        The catalogue also contains E₆/E₇/E₈ and additional construction models;
        the [scope section](#comparison-scope) records which are outside that theorem.

        <a id="same-group"></a>

        ## 1. Different models of the same group

        | Group or family | Models | Domain | Identification certificate |
        |---|---|---|---|
      MD
      %w[family.PSL family.B family.C family.D].each do |id|
        entry=registry.fetch('entries').find { |e|e['id']==id }
        c=edges(id).fetch(0)
        domain={'family.PSL'=>'rank n ≥ 1','family.B'=>'rank n ≥ 2','family.C'=>'rank n ≥ 2','family.D'=>'rank n ≥ 4'}.fetch(id)
        text<<"| [#{entry.dig('presentation','label') || entry['label']}](##{anchor(id)}) | #{models.fetch(id).map { |m|short_label(m) }.join(' · ')} | #{domain}; every finite field | [Lean certificate](ISOMORPHISMS.md##{c['id']}) |\n"
      end
      text<< <<~MD
        | [G₂(q)](#family-g2) | Octonion · Chevalley | Comparison scope recorded separately | [Local proof / export boundary](#comparison-scope) |
        | [F₄(q)](#family-f4) | Albert · Chevalley | Comparison unfinished | [Open comparison](#comparison-scope) |

        The four included A/B/C/D certificates apply even at nonsimple parameters
        in their domains. They allow results about the original models to be
        transported to the Chevalley models by composing the actual maps.

        Different finite fields of the same size, and different presentations of
        the required field extensions, are identified by
        #{theorem_ref('Atlas.Comparisons.Catalogue.same_label_equiv','Atlas/Comparisons/CatalogueSameLabel.lean','a uniform field-transport certificate')}
        for the models in the comparison registry. The
        [individual transport interfaces](COMPARISONS.md#field-transport) retain
        their precise field and extension hypotheses.

        Each of the 16 sporadic entries currently advertises one construction in
        this catalogue. The aggregate comparison theorem uses the specified Mathieu
        coordinate markings. It does not assert a comparison with an additional
        independently constructed permutation, lattice or other sporadic model.

        <a id="between-families"></a>

        ## 2. Isomorphisms between different families

        Here q is the base-field size, Bₙ/Cₙ/Dₙ use Lie rank, and the subscript in
        PSL_d or PSU_d is the vector-space dimension. A_m without a field parameter
        denotes an alternating group. The classical families use their actual
        projective models.
        These maps have the stated domains even when an endpoint is not simple;
        they do not silently replace a full group by its derived subgroup.

        ### Uniform and low-rank identifications

        | Identification | Parameters | Lean certificates |
        |---|---|---|
        | B₁(q) ≃ C₁(q) ≃ PSU₂(q) ≃ PSL₂(q) | Every finite q; the unitary scalar field has size q² | #{comparison_ref('b1-a1','B₁')} · #{comparison_ref('c1-a1','C₁')} · #{comparison_ref('psu2-a1','PSU₂')} |
        | B₂(q) ≃ C₂(q) | Every finite q | #{comparison_ref('b2-c2')} |
        | Bₙ(q) ≃ Cₙ(q) | Even q, n ≥ 1 | #{comparison_ref('even-b-c')} |
        | D₂⁺(q) ≃ PSL₂(q) × PSL₂(q) | Every finite q; a product, outside the simple D-family range | #{comparison_ref('d2-product')} |
        | D₃⁺(q) ≃ PSL₄(q) | Every finite q | #{comparison_ref('d3-a3')} |
        | ²D₂(q) ≃ PSL₂(q²) | Every finite q; PSL is over the quadratic extension | #{comparison_ref('minus-d2-a1')} |
        | ²D₃(q) ≃ PSU₄(q) | Every finite q; common quadratic extension | #{comparison_ref('minus-d3-unitary')} |

        ### Exceptional identifications at small parameters

        | Order | Isomorphic groups | Lean certificates |
        |---:|---|---|
        | 60 | PSL₂(4) ≃ PSL₂(5) ≃ A₅ | #{comparison_ref('psl2-four-a5','q = 4')} · #{comparison_ref('psl2-five-a5','q = 5')} |
        | 168 | PSL₃(2) ≃ PSL₂(7) | #{comparison_ref('psl2-seven-psl3-two')} |
        | 360 | PSL₂(9) ≃ A₆ ≃ C₂(2)′ ≃ B₂(2)′ | #{comparison_ref('psl2-nine-a6','PSL₂/A₆')} · #{comparison_ref('c2-derived-a6','derived C₂')} · #{comparison_ref('b2-derived-c2-derived','derived B₂')} |
        | 20,160 | PSL₄(2) ≃ D₃⁺(2) ≃ A₈ | #{comparison_ref('psl4-two-a8','PSL₄/A₈')} · #{comparison_ref('a8-d3-two','D₃/A₈')} |
        | 25,920 | PSU₄(2) ≃ ²D₃(2) ≃ C₂(3) ≃ B₂(3) | #{comparison_ref('psu4-card2-c2-card3','PSU₄/C₂')} · #{comparison_ref('minus-d3-card2-c2-card3','²D₃/C₂')} · #{comparison_ref('psu4-card2-b2-card3','PSU₄/B₂')} |

        At the excluded binary parameter the **full** groups B₂(2) and C₂(2)
        are isomorphic to S₆, of order 720
        (#{comparison_ref('b2-card2-s6','B₂ certificate')},
        #{comparison_ref('c2-card2-s6','C₂ certificate')}). Their derived subgroups
        are the order-360 groups above. PSL₃(4), although also of order 20,160,
        is separated from A₈ below.

        The [complete interface index](COMPARISONS.md#between-families) includes
        the compositions, arbitrary-field versions and canonical-field wrappers.

        <a id="remaining-pairs"></a>

        ## 3. All remaining pairs: one certificate, orders and invariants

        **Within the comparison theorem's stated scope, different normalized labels
        imply nonisomorphic groups.** A normalized label records the family and
        parameters after the proved identifications above have been applied.
        The single certificate covering all such pairs is
        #{theorem_ref('Atlas.Comparisons.Catalogue.not_isomorphic_of_normalized_label_ne',main)}.
        Its parent theorem,
        #{theorem_ref('Atlas.Comparisons.Catalogue.isomorphic_iff_normalized_label_eq',main)},
        proves both directions: isomorphism holds exactly when normalized labels agree.

        The certificate combines the following two ways of separating groups.

        ### Different orders

        The group-order bridge
        #{theorem_ref('Atlas.Comparisons.Catalogue.card','Atlas/Comparisons/CatalogueCardinality.lean','card')}
        proves the exact order of every model in the comparison registry. The
        arithmetic theorem
        #{theorem_ref('Atlas.OrderArithmetic.catalogue_orders_distinct',arithmetic)}
        proves unequal orders whenever normalized labels differ and the pair is
        outside the two exceptional patterns below. This is uniform in the
        admissible ranks and field sizes, not a bounded numerical search.

        #{theorem_ref('Atlas.Comparisons.not_isomorphic_of_card_ne','Atlas/Comparisons/Cardinality.lean')}
        converts unequal orders into nonisomorphism; the combined registry-level
        certificate is
        #{theorem_ref('Atlas.Comparisons.Catalogue.not_isomorphic_of_not_collision','Atlas/Comparisons/CatalogueCardinality.lean')}.
        The [complete order-collision theorem](../Atlas/OrderArithmetic/Classification.lean)
        proves that no further equal-order patterns occur in this scope.

        In particular, the 16 completed sporadic groups and Tits have pairwise
        different orders, and their orders differ from all admissible values of
        the 13 families in this comparison registry. They are therefore covered
        by the same order and nonisomorphism certificates.

        ### Equal orders, separated by one invariant

        | Nonisomorphic groups | Domain and common order | Separating invariant | Lean certificates |
        |---|---|---|---|
        | Bₙ(q), Cₙ(q) | Odd q, n ≥ 3; their proved order formulas agree | Number of conjugacy classes of involutions: n versus ⌊n/2⌋ + 1 | #{comparison_ref('odd-b-c-order','equal order')} · #{theorem_ref('Atlas.Comparisons.Classical.oddB_C_involution_counts','Atlas/Comparisons/Classical/OrthogonalInvolutions.lean','counts')} · #{comparison_ref('odd-b-c-distinct','nonisomorphism')} |
        | A₈ ≃ PSL₄(2), PSL₃(4) | Both order 20,160 | Center of a Sylow-2 subgroup: order 2 versus order 4 | #{comparison_ref('a8-psl3-four-order','equal order')} · #{comparison_ref('psl4-two-psl3-four-distinct','PSL certificate')} · #{comparison_ref('a8-psl3-four-distinct','A₈ certificate')} |

        The invariants are themselves preserved by isomorphism:
        #{theorem_ref('Atlas.k2_mulEquiv','Atlas/GroupTheory/InvolutionClasses.lean','involution-class invariance')}
        and #{theorem_ref('Atlas.GroupTheory.sylow_center_card_eq_of_mulEquiv','Atlas/GroupTheory/SylowCenterInvariant.lean','Sylow-center invariance')}.
        #{theorem_ref('Atlas.Comparisons.Catalogue.exceptional_not_isomorphic','Atlas/Comparisons/CatalogueObstructions.lean','One combined obstruction certificate')}
        handles both exceptional patterns, including field transport and reversal
        of the two endpoints. Rank two and even-characteristic B/C pairs belong
        to the isomorphism table, not this obstruction table.

        <a id="comparison-scope"></a>

        ## Scope, remaining gaps and verification

        The aggregate theorem covers Cₚ, A_m, PSL, PSU, B, C, D⁺, D⁻, G₂, F₄,
        ³D₄, ²B₂ and ²G₂, together with all 16 completed sporadic groups and Tits.
        Its [exact simple parameter ranges and model definitions](../COMPARISON.md#scope-and-definitions)
        remain part of the statement. The low-rank and derived-group maps above
        are additional interfaces; they are not additional registry constructors.

        | Outside the aggregate theorem or exported comparison certificates | Present status |
        |---|---|
        | E₆, E₇, E₈ | Their actual models have separate Lean order and simplicity proofs, but the comparison registry and its exhaustive order-collision theorem do not include them. No blanket nonisomorphism result involving these families is asserted here. |
        | Chevalley G₂ versus Octonion G₂ | A marked equivalence has ten passed local audit scopes; its final preservation/registration and source export are outside this review snapshot. The exported comparison theorem uses the Octonion model. |
        | Chevalley F₄ versus Albert F₄ | The identification is unfinished. The exported comparison theorem uses the Albert model. |
        | G₂(2)′ versus PSU₃(3), order 6,048 | The derived-group bridge is unfinished; equality of orders is not a certificate of isomorphism. |
        | ²G₂(3)′ versus PSL₂(8), order 504 | The derived-group bridge is unfinished; the full small-parameter group must remain distinct from its derived subgroup. |

        E₆/E₇/E₈ order formulas can be used with the general unequal-cardinality
        lemma once a particular inequality has been proved. Having the formulas
        alone does not extend the exhaustive comparison theorem to these families.

        The aggregate theorem has a passed
        [full dependency audit](../verification/runs/comparison-catalogue-isomorphism/20261012T065332-1260019/RESULT.json)
        and [verbatim compiled statements](../verification/comparisons/THEOREM_STATEMENTS.txt).
        Its two independent Comparator replays remain memory-stopped, as recorded
        in the [dated receipt](../verification/existence/2026-10-25-draft/Catalogue-isomorphism/RESULT.json).
        The [four invariant contracts](../verification/existence/RESULTS.md) passed
        separately. Their success does not turn the aggregate replay into a pass.

        <a id="construction-inventory"></a>

        ## Construction inventory

        The 33 completed entries retain all 39 displayed models, including the six
        additional Chevalley constructions. Open a group name for its model definitions,
        orders, simplicity domains and construction-identification certificates.

      MD
      text
    end
    def comparison_interfaces
      text=<<~MD
        # Comparison certificates: complete interface index

        The [construction and identification guide](REALIZATIONS.md) explains the
        mathematical conclusions. This index retains every registered interface
        and its exact parameter assumptions, grouped by the question it answers.
        [One aggregate certificate](REALIZATIONS.md#remaining-pairs) covers all
        nonisomorphic pairs in its [stated scope](REALIZATIONS.md#comparison-scope).

        ## Different construction models

        | Family | Models | Proved domain | Certificate |
        |---|---|---|---|
      MD
      comparisons.each do |c|
        id=c.dig('source','qualified_id').split('/').first
        entry=registry.fetch('entries').find { |e|e['id']==id }
        text<<"| #{entry.dig('presentation','label') || entry['label']} | #{models.fetch(id).map { |m|short_label(m) }.join(' · ')} | #{c.dig('parameter_domain','description')} | #{certificate(c,'../')} |\n"
      end
      text<<"\nG₂/F₄ comparisons retain their [separate scopes](REALIZATIONS.md#comparison-scope).\n\n"
      groups=[
        ['field-transport','Field and extension transport',%w[b-field d-field unitary-field minus-d-field]],
        ['between-families','Uniform and low-rank isomorphisms',%w[b1-a1 c1-a1 psu2-a1 psu2-c1 psu2-b1 even-b-c b2-c2 d2-product d3-a3 minus-d2-a1 minus-d3-unitary]],
        ['small-parameters','Exceptional and small-parameter isomorphisms',%w[psl2-four-a5 psl2-five-a5 psl2-four-five psl2-seven-psl3-two psl2-nine-a6 psl2-nine-canonical-a6 b2-derived-c2-derived c2-derived-a6 psl2-nine-b2-derived psl2-nine-c2-derived a8-d3-two psl4-two-a8 psu4-binary-c2-ternary psu4-card2-c2-card3 minus-d3-card2-c2-card3 psu4-card2-b2-card3 c2-binary-s6 c2-card2-s6 b2-card2-s6]],
        ['equal-order-separation','Equal-order and nonisomorphism certificates',%w[odd-b-c-order odd-b-c-distinct psl4-two-psl3-four-order a8-psl3-four-order psl4-two-psl3-four-distinct a8-psl3-four-distinct]]
      ]
      by_id=comparison_rows.to_h { |r|[r['id'],r] }
      raise 'Comparison index must partition every registered interface exactly once' unless groups.flat_map(&:last).sort==by_id.keys.sort
      groups.each do |id,title,ids|
        text<<"<a id=\"#{id}\"></a>\n\n## #{title}\n\n| Groups | Conclusion | Parameters | Lean certificate |\n|---|---|---|---|\n"
        ids.each do |rid|
          r=by_id.fetch(rid)
          relation={'isomorphism'=>'Isomorphic','same_order'=>'Equal order','nonisomorphism'=>'Nonisomorphic'}.fetch(r['relation'])
          cells=[r['left']+' / '+r['right'],relation,r['parameters'],source(r,'../')].map { |v|v.gsub('|','\\|') }
          text<<"| #{cells.join(' | ')} |\n"
        end
        text<<"\n"
      end
      text<<"These 40 registered interfaces supplement the [aggregate comparison and order certificates](REALIZATIONS.md#remaining-pairs). All current coverage limits and unfinished bridges are listed in [one scope section](REALIZATIONS.md#comparison-scope).\n"
      text
    end
    def isomorphism_page(statements)
      text="# Lean certificates identifying construction models\n\nThese are actual `MulEquiv` terms between the named concrete carriers. Their\nverbatim compiled types come from the source-bound 26 October audit. The linked\nLean definitions contain the proofs; the separate full audits retain type, instance\nand proof dependencies. A certificate applies on its stated domain, including\nnonsimple parameters when specified. Order equality alone is not an identification.\n\n"
      text+="This is the technical appendix for the four included construction-identification maps. The [comparison guide](REALIZATIONS.md) also covers [isomorphisms between families](REALIZATIONS.md#between-families), [nonisomorphism by orders and invariants](REALIZATIONS.md#remaining-pairs), and [remaining gaps](REALIZATIONS.md#comparison-scope).\n\n"
      comparisons.each do |c|
        text+="<a id=\"#{c['id']}\"></a>\n\n## #{c.dig('source','qualified_id')} ≃ #{c.dig('target','qualified_id')}\n\n"
        text+="Domain: #{c.dig('parameter_domain','description')}.\n\n"
        text+="| Interface | Exact Lean reference |\n|---|---|\n"
        [['Source model',c.dig('source','carrier')],['Source group operations',c.dig('source','group_instance')],
          ['Target model',c.dig('target','carrier')],['Target group operations',c.dig('target','group_instance')],
          ['Parameter map',c['parameter_map']],['Isomorphism witness',c['witness']]].each { |title,ref|text+="| #{title} | #{source(ref,'../')} |\n" }
        s=statements.fetch(c.dig('witness','declaration'))
        text+="\nProof definition (verbatim source, in namespace `Atlas.Chevalley.Catalogue`):\n\n```lean\n#{proof_source(c['witness'])}\n```\n\n"
        text+="<details>\n<summary>Complete compiled type, including implicit instances</summary>\n\n```lean\n#{s[:text].rstrip}\n```\n\n</details>\n\n[Compiled evidence](../#{s[:path]}) · [Full dependency audit](../#{c.dig('evidence','directory')}).\n\n"
        text+="Marked-generator compatibility:\n\n"+c.fetch('compatibility').map { |r|"- #{source(r,'../')}" }.join("\n")+"\n\n"
      end
      multiple.each_key do |id|
        next unless edges(id).empty?
        text+="## #{id}: comparison scope\n\n#{comparison_status(id)}\n\n[Both constructions](../CATALOGUE.md##{anchor(id)}).\n\n"
      end
      text
    end
    def diagram_block(e)
      id=e.fetch('id');ms=models.fetch(id)
      links=ms.map { |m|"<a href=\"../../../CATALOGUE.md##{model_anchor(m)}\">#{CGI.escapeHTML(m['label'])}</a>" }
      c=edges(id).map { |edge|"<a href=\"../../../catalogue/ISOMORPHISMS.md##{edge['id']}\">Lean isomorphism certificate</a>" }
      note=ms.size>1 && c.empty? ? " <span>#{CGI.escapeHTML(comparison_status(id))}</span>" : ''
      "<!-- ATLAS_MODELS_BEGIN -->\n<p class=\"model-navigation\"><strong>Construction shown:</strong> #{CGI.escapeHTML(ms.first['label'])}. " +
        "<strong>Available constructions:</strong> #{links.join(' · ')}. #{c.join(' · ')}#{note}</p>\n<!-- ATLAS_MODELS_END -->\n"
    end
    def render_diagrams(mode)
      binding=read_json('catalogue/model-presentation.json')
      measurement=read_json('catalogue/measurement.json')
      diagrams=read_json('verification/release-candidate/DIAGRAM_BINDING.json')
      registry.fetch('entries').each do |e|
        p=e.fetch('proof_dependencies');html=File.read(@root+'/'+p)
        original=html.gsub(/<!-- ATLAS_MODELS_BEGIN -->.*?<!-- ATLAS_MODELS_END -->\n/m,'')
        b=binding.fetch('diagrams').fetch(p)
        raise "Underlying diagram changed: #{p}" unless Digest::SHA256.hexdigest(original)==b.fetch('original_html_sha256')
        data=original[/<script id="data" type="application\/json">(.*?)<\/script>/m,1]
        raise 'Changed mathematical graph data' unless Digest::SHA256.hexdigest(data)==b.fetch('graph_data_sha256')
        raise 'Missing diagram header insertion point' unless original.include?('<p id="stats">')
        updated=original.sub('<p id="stats">',diagram_block(e)+'<p id="stats">')
        if mode=='refresh'
          File.write(@root+'/'+p,updated)
        else
          raise "Stale construction navigation: #{p}" unless html==updated
        end
        h=Digest::SHA256.hexdigest(updated)
        measurement.fetch('entries').fetch(e['id'])['diagram_sha256']=h
        diagrams.fetch('groups').fetch(e['id'])['sha256']=h
      end
      diagrams['presentation_binding']='catalogue/model-presentation.json'
      diagrams['presentation_scope']='Construction navigation added; original graph data, roots, counts and source hashes unchanged'
      {'catalogue/measurement.json'=>measurement,'verification/release-candidate/DIAGRAM_BINDING.json'=>diagrams}.each do |p,j|
        text=JSON.pretty_generate(j)+"\n"
        mode=='refresh' ? File.write(@root+'/'+p,text) : (raise "Stale diagram presentation binding #{p}" unless File.read(@root+'/'+p)==text)
      end
    end
  end
end
