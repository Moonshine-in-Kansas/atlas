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
      text=models.fetch(id).map { |m|"[#{m['label']}](#{prefix}CATALOGUE.md##{model_anchor(m)})" }.join('<br>')
      edges(id).each { |c|text+='<br>'+certificate(c,prefix) }
      text
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
    def isomorphism_page(statements)
      text="# Lean certificates identifying construction models\n\nThese are actual `MulEquiv` terms between the named concrete carriers. Their\nverbatim compiled types come from the source-bound 26 October audit. The linked\nLean definitions contain the proofs; the separate full audits retain type, instance\nand proof dependencies. A certificate applies on its stated domain, including\nnonsimple parameters when specified. Order equality alone is not an identification.\n\n"
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
