# Present all recorded models without changing mathematical registrations.
require 'json'
require 'cgi'
require 'digest'
require 'date'
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
        if m['default']
          e.dig('presentation','supplemental_statements').to_a.each do |ref|
            text+="| #{ref.fetch('label')} | #{source(ref,prefix)} · #{audit_link(ref.fetch('audit'),[ref.fetch('declaration')]).gsub('(../','('+prefix)} |\n"
          end
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
            text+="This contract proves order and simplicity of this explicit witness for #{range}.\n\n"
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
    def supplemental_statement_names
      registry.fetch('entries').flat_map { |e|e.dig('presentation','supplemental_statements').to_a.map { |r|r.fetch('declaration') } }
    end
    def comparison_rows
      data=read_json('catalogue/comparisons.json')
      data.fetch('entries')+data.fetch('supplements').flat_map { |s|s.fetch('entries') }
    end
    AGGREGATE_AUDIT='verification/runs/comparison-catalogue-isomorphism/20261012T065332-1260019'
    def statement(ref,title='Lean statement')
      "[#{title}](#{link(ref,'../')} \"#{ref.fetch('declaration')}\")"
    end
    def theorem_ref(name,path,title='Lean statement')
      statement({'declaration'=>name,'source'=>path},title)
    end
    def audit_link(directory,names,title=nil)
      @audit_names||={}
      @audit_dates||={}
      unless @audit_names.key?(directory)
        result=read_json(directory+'/RESULT.json')
        raise "Audit not passed/full: #{directory}" unless result['status']=='passed' && result['mode']=='full'
        @audit_dates[directory]=Date.parse(result.fetch('finished_utc')).strftime('%d %b')
        @audit_names[directory]=read_json(directory+'/CHECKPOINT.json').fetch('targets').map { |t|t.fetch('declaration') }
      end
      missing=names-@audit_names.fetch(directory)
      unless missing.empty?
        # Supporting order-arithmetic lemmas can be transitive dependencies rather
        # than audit roots. Require their actual presence in the complete graph.
        require 'zlib'
        Zlib::GzipReader.open(@root+'/'+directory+'/dependencies.jsonl.gz') do |io|
          io.each_line do |line|
            next unless missing.any? { |n|line.include?(n) }
            name=JSON.parse(line).fetch('name')
            if missing.delete(name)
              @audit_names[directory]<<name
              break if missing.empty?
            end
          end
        end
        raise "Certificate omits declarations: #{missing.join(', ')}" unless missing.empty?
      end
      "[#{title || "Passed audit (#{@audit_dates.fetch(directory)})"}](../#{directory}/CERTIFICATE.md)"
    end
    def comparison_evidence
      data=read_json('catalogue/comparisons.json')
      [data,*data.fetch('supplements')].flat_map do |part|
        part.fetch('entries').map { |r|[r.fetch('id'),part.fetch('evidence').fetch('directory')] }
      end.to_h
    end
    def model_order_audit
      directory=read_json('verification/current.json').fetch('supplemental_cache_audit').fetch('directory')
      result=read_json(directory+'/RESULT.json')
      raise 'Model audit not passed' unless result['status']=='passed-source-bound-cache-audit'
      names=File.readlines(@root+'/'+directory+'/declarations.jsonl').map { |line|JSON.parse(line).fetch('declaration') }
      orders=registry.fetch('entries').map { |e|e.dig('roles','order','declaration') }
      raise 'Model audit omits catalogue orders' unless (orders-names).empty?
      "[Compiled model audit (26 Oct)](../#{directory}/RESULT.json)"
    end
    def comparison_links(ids)
      rows=ids.map { |id|comparison_rows.find { |r|r['id']==id } || (raise "Unknown comparison #{id}") }
      labels={'b1-a1'=>'B₁','c1-a1'=>'C₁','psu2-a1'=>'PSU₂',
        'psl2-four-a5'=>'q = 4','psl2-five-a5'=>'q = 5','psl2-nine-a6'=>'PSL₂/A₆',
        'c2-derived-a6'=>'C₂′/A₆','b2-derived-c2-derived'=>'B₂′/C₂′',
        'b2-card2-s6'=>'B₂/S₆','c2-card2-s6'=>'C₂/S₆',
        'psl4-two-a8'=>'PSL₄/A₈','a8-d3-two'=>'A₈/D₃',
        'psu4-card2-c2-card3'=>'PSU₄/C₂','minus-d3-card2-c2-card3'=>'²D₃/C₂',
        'psu4-card2-b2-card3'=>'PSU₄/B₂','odd-b-c-order'=>'equal order',
        'odd-b-c-distinct'=>'nonisomorphism','a8-psl3-four-order'=>'equal order',
        'a8-psl3-four-distinct'=>'A₈ nonisomorphism','psl4-two-psl3-four-distinct'=>'PSL₄ nonisomorphism'}
      proofs=rows.map { |r|statement(r,rows.size==1 ? 'statement' : labels.fetch(r.fetch('id'))) }.join(' · ')
      audits=rows.group_by { |r|comparison_evidence.fetch(r.fetch('id')) }.map do |directory,rs|
        audit_link(directory,rs.map { |r|r.fetch('declaration') })
      end.join(' · ')
      [proofs,audits]
    end
    def compact_inventory
      text="<a id=\"construction-inventory\"></a>\n\n<details>\n<summary>Reference: all 39 construction models (33 catalogue entries)</summary>\n\nDefinitions and full parameter ranges are retained in the [catalogue](../CATALOGUE.md).\n\n"
      registry.fetch('entries').each do |entry|
        id=entry.fetch('id');label=entry.dig('presentation','label') || entry.fetch('label')
        text<<"<a id=\"#{anchor(id)}\"></a>\n\n**[#{label}](../CATALOGUE.md##{anchor(id)})**\n\n"
        models.fetch(id).each do |m|
          text<<"<a id=\"#{model_anchor(m)}\"></a>\n\n- #{short_label(m)}: #{source(m.fetch('carrier'),'../')}\n"
        end
        text<<"\n"
      end
      text<<"</details>\n\n"
    end
    def exceptional_groups
      [
        ['B₁(q) ≃ C₁(q) ≃ PSU₂(q) ≃ PSL₂(q); every finite q',%w[b1-a1 c1-a1 psu2-a1]],
        ['B₂(q) ≃ C₂(q); every finite q',%w[b2-c2]],
        ['Bₙ(q) ≃ Cₙ(q); even q, n ≥ 1',%w[even-b-c]],
        ['D₂⁺(q) ≃ PSL₂(q) × PSL₂(q); every finite q (a product)',%w[d2-product]],
        ['D₃⁺(q) ≃ PSL₄(q); every finite q',%w[d3-a3]],
        ['²D₂(q) ≃ PSL₂(q²); every finite q',%w[minus-d2-a1]],
        ['²D₃(q) ≃ PSU₄(q); every finite q',%w[minus-d3-unitary]],
        ['PSL₂(4) ≃ PSL₂(5) ≃ A₅; order 60',%w[psl2-four-a5 psl2-five-a5]],
        ['PSL₃(2) ≃ PSL₂(7); order 168',%w[psl2-seven-psl3-two]],
        ['PSL₂(9) ≃ A₆ ≃ C₂(2)′ ≃ B₂(2)′; order 360',%w[psl2-nine-a6 c2-derived-a6 b2-derived-c2-derived]],
        ['B₂(2) ≃ C₂(2) ≃ S₆; full groups, order 720',%w[b2-card2-s6 c2-card2-s6]],
        ['PSL₄(2) ≃ D₃⁺(2) ≃ A₈; order 20,160',%w[psl4-two-a8 a8-d3-two]],
        ['PSU₄(2) ≃ ²D₃(2) ≃ C₂(3) ≃ B₂(3); order 25,920',%w[psu4-card2-c2-card3 minus-d3-card2-c2-card3 psu4-card2-b2-card3]]
      ]
    end
    def comparison_guide
      text=<<~MD
        # Constructions and identification certificates
    
        Each result below has a **Lean statement** and a separate **verification certificate**.
        Certificates record passed full dependency audits; independent Comparator results
        are identified separately. Here q is a finite-field size, B/C/D subscripts are
        Lie ranks, and PSL/PSU subscripts are dimensions. A_m denotes an alternating group.
    
        <a id="same-group"></a>
    
        ## 1. Isomorphisms between different models
    
        | Models and domain | Lean statement | Verification certificate |
        |---|---|---|
      MD
      %w[family.PSL family.B family.C family.D].each do |id|
        c=edges(id).fetch(0)
        entry=registry.fetch('entries').find { |e|e['id']==id }
        label=entry.dig('presentation','label') || entry.fetch('label')
        domain={'family.PSL'=>'n ≥ 1','family.B'=>'n ≥ 2','family.C'=>'n ≥ 2','family.D'=>'n ≥ 4'}.fetch(id)
        names=models.fetch(id).map { |m|short_label(m) }.join(' ≃ ')
        proof="[#{c.dig('witness','declaration').split('.').last}](ISOMORPHISMS.md##{c['id']} \"#{c.dig('witness','declaration')}\")"
        text<<"| #{label}: #{names}; #{domain}, every finite q | #{proof} | #{audit_link(c.dig('evidence','directory'),[c.dig('witness','declaration')])} |\n"
      end
      field_name='Atlas.Comparisons.Catalogue.same_label_equiv'
      text<<"| Same family and parameters over different finite fields or extension presentations of the same sizes; within the comparison registry | #{theorem_ref(field_name,'Atlas/Comparisons/CatalogueSameLabel.lean','statement')} | #{audit_link(AGGREGATE_AUDIT,[field_name])} |\n\n"
      text<< <<~MD
        The A/B/C/D maps also cover nonsimple parameters in the stated domains.
        **G₂:** the Chevalley–Octonion map has ten passed local audit scopes, but its
        final preservation/registration and source export are outside this snapshot.
        **F₄:** the Chevalley–Albert map remains unfinished. Neither is presented as
        an included identification certificate. Each sporadic entry currently has
        one advertised construction; the comparison registry fixes the Mathieu markings.
    
      MD
      text<<compact_inventory
      text<< <<~MD
        <a id="between-families"></a>
    
        ## 2. Exceptional isomorphisms
    
        These identify different family labels: low-rank or characteristic-dependent
        coincidences, and isolated small-parameter coincidences. A prime (′) denotes
        the derived subgroup; full groups and derived subgroups are separate endpoints.
        In unitary and minus-orthogonal notation q is the base-field size and the
        scalar field has size q².
    
        | Isomorphism and domain | Lean statements | Verification certificates |
        |---|---|---|
      MD
      exceptional_groups.each do |description,ids|
        proofs,audits=comparison_links(ids)
        text<<"| #{description} | #{proofs} | #{audits} |\n"
      end
      text<< <<~MD
    
        **Still open in this snapshot:** the bridges G₂(2)′ ≃ PSU₃(3) (order 6,048)
        and ²G₂(3)′ ≃ PSL₂(8) (order 504). Their equal orders are not identification
        certificates. The [complete statement index](COMPARISONS.md#between-families)
        retains all compositions, canonical-field wrappers and full hypotheses.
    
        <a id="remaining-pairs"></a>
    
        ## 3. Non-isomorphisms of all other cases
    
        After the exceptional isomorphisms in Theme 2, the remaining distinct
        normalized labels are separated by unequal orders or one of the two
        invariants below. The order argument combines the proved cardinalities
        of the constructed models with the uniform numerical classification.
    
        | Non-isomorphism result and reason | Lean statements | Verification certificates |
        |---|---|---|
      MD
      general='Atlas.Comparisons.Catalogue.not_isomorphic_of_normalized_label_ne'
      order='Atlas.OrderArithmetic.catalogue_order_eq_iff'
      generic='Atlas.Comparisons.not_isomorphic_of_card_ne'
      text<<"| **Combined comparison theorem:** distinct normalized labels give nonisomorphic groups within its [specified registry](../COMPARISON.md#scope-and-definitions) | #{theorem_ref(general,'Atlas/Comparisons.lean','statement')} | #{audit_link(AGGREGATE_AUDIT,[general])} |\n"
      text<<"| <a id=\"order-certificates\"></a><a id=\"e-series-order\"></a> **By order:** outside the listed isomorphisms and the two patterns below, orders differ. The numerical classification is uniform, with no bound on rank or field size. | [Model orders](../THEOREM_STATEMENTS.md) · #{theorem_ref(order,'Atlas/OrderArithmetic/Classification.lean','order classification')} · #{theorem_ref('Atlas.OrderArithmetic.catalogue_order_ne','Atlas/OrderArithmetic/Classification.lean','unequal orders')} · #{theorem_ref(generic,'Atlas/Comparisons/Cardinality.lean','unequal orders imply nonisomorphism')} | #{model_order_audit} · #{audit_link(AGGREGATE_AUDIT,[order,'Atlas.OrderArithmetic.catalogue_order_ne',generic])} |\n"
      counts='Atlas.Comparisons.Classical.oddB_C_involution_counts'
      bc_proofs,bc_audit=comparison_links(%w[odd-b-c-order odd-b-c-distinct])
      text<<"| **Equal order, different involution-class counts:** Bₙ(q) and Cₙ(q), odd q and n ≥ 3; counts n and ⌊n/2⌋ + 1 | #{bc_proofs} · #{theorem_ref(counts,'Atlas/Comparisons/Classical/OrthogonalInvolutions.lean','counts')} | #{bc_audit} · [B invariant replay](../verification/existence/2026-10-25-draft/AtlasDistinguished-typeB/RESULT.json) · [C invariant replay](../verification/existence/2026-10-25-draft/AtlasDistinguished-typeC/RESULT.json) |\n"
      a_proofs,a_audit=comparison_links(%w[a8-psl3-four-order a8-psl3-four-distinct psl4-two-psl3-four-distinct])
      text<<"| **Equal order, different Sylow-2 centers:** A₈ ≃ PSL₄(2) versus PSL₃(4), both order 20,160; center sizes 2 and 4 | #{a_proofs} | #{a_audit} · [A₈ invariant replay](../verification/existence/2026-10-25-draft/AtlasDistinguished-alternating8/RESULT.json) · [PSL₃(4) invariant replay](../verification/existence/2026-10-25-draft/AtlasDistinguished-psl3Four/RESULT.json) |\n"
      text<< <<~MD
    
        A normalized label is the family and parameter label after the proved
        exceptional identifications. The 16 completed sporadic groups and Tits are
        separated from one another and from all admissible values of the 16 completed
        families by order. The four invariant replays passed separately. The
        [two aggregate Comparator replays](../verification/existence/2026-10-25-draft/Catalogue-isomorphism/RESULT.json)
        remain memory-stopped; the passed full audits above do not assert a replay pass.
    
        <a id="comparison-scope"></a>
    
        The linked statements retain their exact model and parameter hypotheses.
        The combined theorem's registry is specified in the [technical description](../COMPARISON.md#scope-and-definitions).
        For G₂/F₄ the registry uses the Octonion/Albert models; the comparisons to
        their Chevalley models have the status in Theme 1. The unfinished derived-group
        bridges in Theme 2 remain separate. [Exact theorem and compiled statements](../COMPARISON.md).
      MD
      text
    end
    def comparison_interfaces
      text=<<~MD
        # Lean statements and verification certificates
    
        This reference follows the same three themes as the [comparison guide](REALIZATIONS.md).
        Every row links the exact Lean statement and the passed full dependency audit
        containing it. Parameter hypotheses are retained verbatim from the registry.
    
        <a id="same-group"></a>
    
        ## 1. Isomorphisms between different models
    
        | Models | Domain | Lean statement | Verification certificate |
        |---|---|---|---|
      MD
      comparisons.each do |c|
        id=c.dig('source','qualified_id').split('/').first
        entry=registry.fetch('entries').find { |e|e['id']==id }
        text<<"| #{entry.dig('presentation','label') || entry['label']}: #{models.fetch(id).map { |m|short_label(m) }.join(' ≃ ')} | #{c.dig('parameter_domain','description')} | #{source(c.fetch('witness'),'../')} · #{certificate(c,'../')} | #{audit_link(c.dig('evidence','directory'),[c.dig('witness','declaration')])} |\n"
      end
      text<<"\nG₂/F₄ and sporadic model scopes are stated in [Theme 1](REALIZATIONS.md#same-group).\n\n<a id=\"field-transport\"></a>\n\n"
      groups=[
        ['field-transport',nil,%w[b-field d-field unitary-field minus-d-field]],
        ['between-families','2. Exceptional isomorphisms',%w[b1-a1 c1-a1 psu2-a1 psu2-c1 psu2-b1 even-b-c b2-c2 d2-product d3-a3 minus-d2-a1 minus-d3-unitary psl2-four-a5 psl2-five-a5 psl2-four-five psl2-seven-psl3-two psl2-nine-a6 psl2-nine-canonical-a6 b2-derived-c2-derived c2-derived-a6 psl2-nine-b2-derived psl2-nine-c2-derived a8-d3-two psl4-two-a8 psu4-binary-c2-ternary psu4-card2-c2-card3 minus-d3-card2-c2-card3 psu4-card2-b2-card3 c2-binary-s6 c2-card2-s6 b2-card2-s6]],
        ['remaining-pairs','3. Non-isomorphisms of all other cases',%w[odd-b-c-order odd-b-c-distinct psl4-two-psl3-four-order a8-psl3-four-order psl4-two-psl3-four-distinct a8-psl3-four-distinct]]
      ]
      by_id=comparison_rows.to_h { |r|[r['id'],r] }
      raise 'Comparison index must partition every interface exactly once' unless groups.flat_map(&:last).sort==by_id.keys.sort
      groups.each do |id,title,ids|
        text<<"<a id=\"#{id}\"></a>\n\n## #{title}\n\n" if title
        text<<"<a id=\"small-parameters\"></a>\n\n" if id=='between-families'
        if id=='remaining-pairs'
          name='Atlas.Comparisons.Catalogue.not_isomorphic_of_normalized_label_ne'
          text<<"One statement covers all distinct normalized labels in the [exact scope](REALIZATIONS.md#comparison-scope): #{theorem_ref(name,'Atlas/Comparisons.lean',name)}; #{audit_link(AGGREGATE_AUDIT,[name])}. Its [order and invariant cases](REALIZATIONS.md#remaining-pairs) are explained in the guide.\n\n<a id=\"equal-order-separation\"></a>\n\n"
        end
        text<<"| Groups | Conclusion | Parameters | Lean statement | Verification certificate |\n|---|---|---|---|---|\n"
        ids.each do |rid|
          r=by_id.fetch(rid)
          relation={'isomorphism'=>'Isomorphic','same_order'=>'Equal order','nonisomorphism'=>'Nonisomorphic'}.fetch(r['relation'])
          evidence=audit_link(comparison_evidence.fetch(rid),[r.fetch('declaration')])
          cells=[r['left']+' / '+r['right'],relation,r['parameters'],source(r,'../'),evidence].map { |v|v.gsub('|','\\|') }
          text<<"| #{cells.join(' | ')} |\n"
        end
        text<<"\n"
      end
      text<<"All 40 comparison interfaces are retained. The [model-order statements](../THEOREM_STATEMENTS.md) and [verification records](../AUDIT.md) supply the group cardinalities used in the order argument. [Independent replay status](REALIZATIONS.md#remaining-pairs) remains explicit.\n"
      text
    end
    def isomorphism_page(statements)
      text="# Lean certificates identifying construction models\n\nThese are actual `MulEquiv` terms between the named concrete carriers. Their\nverbatim compiled types come from the source-bound 26 October audit. The linked\nLean definitions contain the proofs; the separate full audits retain type, instance\nand proof dependencies. A certificate applies on its stated domain, including\nnonsimple parameters when specified. Order equality alone is not an identification.\n\n"
      text+="This is the technical appendix for the four included construction-identification maps. The [comparison guide](REALIZATIONS.md) also covers [exceptional isomorphisms](REALIZATIONS.md#between-families), [nonisomorphism by orders and invariants](REALIZATIONS.md#remaining-pairs), and [remaining gaps](REALIZATIONS.md#comparison-scope).\n\n"
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
