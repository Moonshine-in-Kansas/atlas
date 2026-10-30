# Read-only applicability checks for exact-export successor evidence.
# This module never runs a proof, builds a cache, or manufactures a receipt.
require 'json'
require 'digest'
require 'zlib'
require 'date'
require 'set'
require_relative 'existence/contracts' unless defined?(AtlasContracts::Index)
require_relative 'policy' unless defined?(AtlasVerification)
require_relative 'parent_receipts'

module AtlasReleaseEvidence
  # Published d2dca87: immutable provenance, not new acceptance evidence.
  BASELINE_INDEX = 'ab2c2390eeba34f6934a3b55a885175725ccfd369652b672e7dcf6719009dc38'.freeze
  BASELINE_MANIFEST = '349815784c90c36b433b24a707faf66bd5cc5546d1956884c1db093abafe28e0'.freeze
  CHECKPOINTS = 'catalogue/checkpoints.json'.freeze
  REGISTRIES = %w[catalogue/catalogue.json catalogue/realizations.json catalogue/comparisons.json].freeze
  # This new policy was authored in canonical names, including two borrowed
  # AlbertEquiv roots. Its source provenance remains the full global inverse.
  CANONICAL_ORIGINAL_SCOPE = 'verification/checkpoints/additions-20261030/f4-registration/f4-catalogue-identification-candidate.json'.freeze
  CANONICAL_ORIGINAL_PATH = 'claude/release-update-v1.2-20261030/g2-catalogue/follow-up/f4-registration-candidate/manifests/f4-catalogue-identification-candidate.json'.freeze
  CANONICAL_ORIGINAL_SHA = 'd974e678e363e5ee275499406eb828e99cc9e31440e18c2674e42648f398e0f6'.freeze

  def self.equal(actual, expected, message)
    raise message unless actual == expected
  end

  def self.checkpoints(files, index)
    path = index['completed_checkpoints']
    return [] unless path
    equal(path, CHECKPOINTS, 'Unexpected completed-checkpoint path')
    raise 'Checkpoint index requires source-update evidence' unless index['source_update']
    data = files.json(path)
    equal(data.values_at('schema_version','kind'), [1,'supplementary-mathematical-results'], 'Unsupported checkpoint schema')
    Date.iso8601(data.fetch('as_of'))
    entries = data.fetch('entries')
    raise 'Empty checkpoint index' if entries.empty?
    ids = entries.map { |e| e.fetch('id') }
    raise 'Invalid or duplicate checkpoint id' unless ids.uniq == ids && ids.all? { |id| id.match?(/\A[a-z0-9][a-z0-9-]*\z/) }
    entries.each do |entry|
      equal(entry.values_at('classification','status'), ['supplementary-mathematical-checkpoint','verified-checkpoint'], 'Checkpoint lacks verified public evidence')
      %w[title parameter_domain].each { |key| raise "Empty checkpoint #{key}" unless entry.fetch(key).is_a?(String) && !entry[key].strip.empty? }
      %w[proved_scope unproved_conclusions].each do |key|
        raise "Checkpoint must state #{key}" unless entry.fetch(key).is_a?(Array) && !entry[key].empty? && entry[key].all? { |s| s.is_a?(String) && !s.strip.empty? }
      end
      refs = entry.fetch('selected_refs')
      raise 'Empty checkpoint references' unless refs.is_a?(Array) && !refs.empty?
      refs.each do |ref|
        expected=reference(ref, files)
        equal(ref.fetch('module'), expected['module'], 'Selected reference module/source mismatch')
        raise 'Selected reference needs exact kind' unless %w[theorem definition].include?(ref.fetch('kind'))
        raise 'Empty selected reference label' unless ref.fetch('label').is_a?(String) && !ref['label'].empty?
        data.fetch('evidence').fetch(ref.fetch('evidence'))
      end
    end
    equal(data.fetch('evidence').keys.sort, entries.flat_map { |e|e['selected_refs'].map { |r|r['evidence'] } }.uniq.sort, 'Unreferenced or missing checkpoint evidence')
    data['evidence'].each_value do |e|
      %w[full_audit manifest].each { |key|equal(files.sha(e.fetch(key)),e.fetch(key+'_sha256'),"Changed checkpoint #{key}") }
      %w[source_binding compiled_statements].each do |key|
        ptr=e.fetch(key);equal(files.sha(ptr.fetch('path')),ptr.fetch('sha256'),"Changed checkpoint #{key}")
      end
      replay=e.fetch('independent_replay')
      equal(replay,{'status'=>'not-claimed-for-current-export','evidence'=>[]},'New independent replay requires a separately reviewed acceptance adapter')
    end
    entries
  end

  def self.reference(ref, files)
    name = ref.fetch('declaration'); path = ref.fetch('source')
    raise 'Invalid declaration reference' unless name.is_a?(String) && name.match?(/\A[^\s`]+\z/)
    raise 'Noncanonical checkpoint source' unless path.match?(%r{\AAtlas/[^\s]+\.lean\z})
    files.path(path)
    {'declaration'=>name, 'module'=>path.delete_suffix('.lean').tr('/', '.'), 'kind'=>'any'}
  end

  def self.cache_artifacts!(files, directory, sources)
    artifacts = files.json(directory+'/CACHE_ARTIFACTS.json')
    expected = sources.keys.grep(/\.lean\z/).map { |p| '.lake/build/lib/lean/'+p.delete_suffix('.lean')+'.olean' }.sort
    equal(artifacts.keys.sort, expected, 'Incomplete portable cache artifact inventory')
    raise 'Invalid artifact hash' unless artifacts.values.all? { |h| h.is_a?(String) && h.match?(/\A[0-9a-f]{64}\z/) }
    equal(files.json(directory+'/CACHE_ARTIFACTS_AFTER.json'), artifacts, 'Audited cache artifacts changed')
  end

  # Kept separate from the catalogue's 33 completed entries and 45 old contracts.
  def self.checkpoint_page(files, index, statements)
    entries = checkpoints(files, index)
    text = "# Completed mathematical checkpoints\n\nThese are completed statements in continuing projects. They do not add completed\nsimple-group catalogue entries or independent Comparator passes. Each signature\nis copied from the exact-export full dependency evidence in the current index.\n\n"
    entries.each do |entry|
      text << "<a id=\"#{entry['id']}\"></a>\n\n## #{entry['title']}\n\nParameters: #{entry['parameter_domain']}\n\nProved scope:\n\n"+entry['proved_scope'].map { |s|"- #{s}\n" }.join
      text << "\nUnproved conclusions:\n\n"+entry['unproved_conclusions'].map { |s|"- #{s}\n" }.join+"\n"
      directory = index.fetch('source_update').fetch('proof_evidence').fetch('directory')
      receipts = files.json(directory+'/ADDITIONS.json')
      evidence = files.json(CHECKPOINTS).fetch('evidence')
      entry['selected_refs'].each do |ref|
        s = statements.fetch(ref.fetch('declaration'))
        e=evidence.fetch(ref.fetch('evidence'))
        text << "### #{ref['label']}\n\n[#{ref['declaration']}](../#{ref['source']}) · [Compiled evidence](../#{s[:path]}) · [Full audit](../#{e['full_audit']}) · [Policy manifest](../#{e['manifest']}).\n\n```lean\n#{s[:text].rstrip}\n```\n\n"
        proofs=receipts.fetch('normal_proof_checks').select { |p|p.fetch('sources').include?(ref['source']) }
        text << proofs.map { |r|"[Normal proof #{r.fetch('id')}](../#{directory}/#{r.fetch('record')})" }.join(' · ')+"\n\n" unless proofs.empty?
      end
    end
    text
  end

  class Successor
    attr_reader :files, :index, :sources, :roots, :directory, :record, :logs, :summary, :previous
    def initialize(files, index, sources, roots, whole: true)
      @files, @index, @sources, @roots = files, index, sources, roots
      @whole = whole
      @pointer = whole ? index.fetch('supplemental_cache_audit') : index.fetch('source_update').fetch('proof_evidence')
      @directory = @pointer.fetch('directory')
      @logs = []
    end

    def equal(a, b, message) = AtlasReleaseEvidence.equal(a, b, message)
    def identities(refs) = refs.map { |r| r.slice('declaration','module') }.uniq.sort_by { |r| r.fetch('declaration') }

    def member(path)
      raise 'Nonportable bundle member' unless path.is_a?(String) && !path.empty? && !path.start_with?('/') && path.split('/').none? { |s| s.empty? || %w[. ..].include?(s) }
      raise "Unbound bundle member #{path}" unless @bundle.fetch('files').key?(path)
      directory + '/' + path
    end

    def json(path)
      full=member(path)
      return files.json(full) unless path.end_with?('.gz')
      Zlib::GzipReader.open(files.path(full)) { |io|JSON.parse(io.read) }
    end

    def each_line(path, &block)
      full = files.path(member(path))
      if path.end_with?('.gz')
        Zlib::GzipReader.open(full) { |io| io.each_line(&block) }
      else
        File.foreach(full, &block)
      end
    end

    def process!(step)
      process = json(step.fetch('record'))
      raise 'Unsuccessful or memory-stopped successor process' unless process['status']=='process-passed' && process['exit_code']==0 && process['signal'].nil? && process['guard_stop'].nil?
      started = DateTime.iso8601(process.fetch('started_utc'))
      finished = DateTime.iso8601(process.fetch('finished_utc'))
      raise 'Historical process cannot be relabelled as successor evidence' unless started.to_date>=@update_date && finished>=started
      digest = Digest::SHA256.new
      each_line(step.fetch('log')) do |line|
        raise 'Error/PANIC/sorry in successor process log' if line.match?(/\berror:|\bPANIC\b|\bsorry\b/)
        digest.update(line)
      end
      equal(digest.hexdigest, process.fetch('log_sha256'), 'Original process/log binding differs')
      process
    end

    def declarations_match!(declarations, targets)
      equal(declarations.map { |d|d.fetch('declaration') }.sort,targets.map { |r|r.fetch('declaration') }.sort,'Incomplete compiled scope declarations')
      declarations.each do |d|
        target=targets.find { |r|r['declaration']==d['declaration'] }
        equal(d.fetch('module'),target.fetch('module'),'Compiled declaration module differs')
        kind=target.fetch('kind')
        raise 'Wrong compiled declaration kind' unless kind=='any' || (kind=='theorem' && d.fetch('theorem')==true) || (kind=='definition' && d.fetch('theorem')==false)
      end
    end

    def checkpoint!(path, targets)
      raise 'Empty policy target selection' if targets.empty?
      checkpoint=json(path)
      equal(checkpoint.fetch('mode'),'full','Checkpoint is not full mode')
      equal(checkpoint.fetch('definitions'),true,'Complete definition inspection required')
      equal(checkpoint.fetch('targets'),targets,'Original checkpoint targets differ')
      equal(checkpoint.fetch('allowed_axioms').sort,AtlasContracts::AXIOMS.sort,'Checkpoint axioms differ')
      checkpoint
    end

    def result!(scope, checkpoint, declarations, graph)
      result=json(scope.fetch('result'))
      equal(result.values_at('status','mode'),%w[passed full],'Scope lacks passed full audit')
      equal(result.fetch('checkpoint'),checkpoint.fetch('id'),'Scope checkpoint identity differs')
      equal(result.fetch('targets'),declarations.size,'Scope result target count differs')
      equal(result.fetch('dependency_nodes'),graph.size,'Scope dependency count differs')
      boundaries=AtlasVerification.check_policy(checkpoint,declarations,graph)
      equal(result.fetch('boundaries'),JSON.parse(JSON.generate(boundaries)),'Recorded boundary outcomes differ')
      equal(result.fetch('axioms').sort,declarations.flat_map { |d|d.fetch('axioms') }.uniq.sort,'Scope axiom summary differs')
      result
    end

    # One actual extraction may discharge many policy scopes. Only this shared
    # graph is retained at a time; slices are recomputed from its exact roots.
    def extraction!(row)
      parent=parent_process_binding!(row,full:true)
      raise 'Public-root audit cannot substitute for addition policies' if @whole==false && parent[:result]['mode']=='audit-public'
      @current_parent=parent
      parent_directory=File.dirname(parent[:result_path])
      if parent[:result]['mode']=='audit-batch'
        evidence=files.json(AtlasParentReceipts.within(parent_directory,'BATCH_EVIDENCE.json'))
        parent[:batch_evidence]=evidence
        batch=evidence.fetch('batch')
        equal(batch.fetch('id'),row.fetch('id'),'Extraction references a different parent batch')
        %w[roots checkpoint result declarations dependencies source_hashes source_hashes_after].each do |field|
          original=AtlasParentReceipts.within(parent_directory,batch.fetch(field))
          equal(files.sha(member(row.fetch(field))),files.sha(original),"Batch artifact differs from original parent: #{field}")
          AtlasParentReceipts.guarded(files,original,parent[:guarded_bindings])
        end
      else
        equal(files.sha(member(row.fetch('checkpoint'))),files.sha(AtlasParentReceipts.within(parent_directory,'MANIFEST.json')),'Extraction checkpoint differs from original parent')
        actual=json(row.fetch('result'))
        adaptation=actual.fetch('adaptation').fetch('original_result')
        equal(adaptation.fetch('sha256'),files.sha(parent[:result_path]),'Full result adapter binds a different original parent')
        expected=parent[:result].merge('status'=>'passed','mode'=>'full')
        equal(actual.slice(*expected.keys),expected,'Full result adapter changed original fields')
        if row['policy_results']
          AtlasParentReceipts.guarded(files,member(row['policy_results']),parent[:guarded_bindings])
        end
      end
      equal(files.sha(member(row.fetch('dependencies'))),parent[:result].fetch(row['dependencies'].end_with?('.gz') ? 'dependency_log_compressed_sha256' : 'dependency_log_sha256'),'Extraction graph differs from original parent')
      equal(files.sha(member(row.fetch('declarations'))),files.sha(AtlasParentReceipts.within(parent_directory,'declarations.jsonl')),'Extraction declarations differ from original parent')
      targets=json(row.fetch('roots'))
      raise 'Empty or duplicate extraction roots' if targets.empty? || targets.map { |r|r.fetch('declaration') }.uniq.size!=targets.size
      checkpoint=checkpoint!(row.fetch('checkpoint'),targets)
      process=process!(row)
      declarations=[]
      each_line(row.fetch('declarations')) { |line|declarations<<JSON.parse(line) }
      declarations_match!(declarations,targets)
      graph={}
      each_line(row.fetch('dependencies')) do |line|
        node=JSON.parse(line);name=node.fetch('name')
        raise 'Duplicate dependency node' if graph.key?(name)
        raise 'Missing type/value dependencies' unless ((node.fetch('type')+node.fetch('value'))-node.fetch('dependencies')).empty?
        graph[name]=node
      end
      raise 'Empty full dependency graph' if graph.empty?
      result!(row,checkpoint,declarations,graph)
      complete=false;printed=[]
      each_line(row.fetch('log')) do |line|
        complete ||= line.strip=="SHARED EXTRACTION COMPLETE: #{targets.size} targets"
        match=line.match(/\ASTATEMENT (\S+) SOURCE (\S+)\s*\z/)
        printed<<{'declaration'=>match[1],'module'=>match[2]} if match
      end
      raise 'Missing completed extraction marker' unless complete
      equal(printed.sort_by { |r|r['declaration'] },identities(targets),'Incomplete compiled type output')
      [targets,declarations,graph,process,parent]
    end

    def policy_inventory!
      path=record['policy_inventory']
      raise 'Missing complete required policy inventory' if !@whole && !path
      return {} unless path
      inventory=json(path)
      equal(inventory.fetch('format'),1,'Unsupported required policy inventory')
      rows=inventory.fetch('entries')
      ids=rows.map { |r|r.fetch('id') }
      raise 'Empty or duplicate required policies' if ids.empty? || ids.uniq!=ids
      rows.each do |r|
        raise 'Unknown policy origin' unless %w[canonical successor source-transported].include?(r.fetch('kind'))
        equal(files.sha(member(r.fetch('manifest'))),r.fetch('sha256'),'Changed required policy hash')
        if r['kind']=='source-transported'
          path,hash=origin_pointer(r)
          equal(files.sha(member(path)),hash,'Changed source-origin map')
          origin_modules!(path)
          original_policy_view!(r)
        else
          raise 'Original naming view on a successor policy' if r.key?('original_policy_view')
        end
      end
      rows.to_h { |r|[r['id'],r] }
    end

    def origin_pointer(row)
      if row['module_transport']
        pointer=row.fetch('module_transport')
        pair=pointer.values_at('path','sha256')
        equal(pair,row.values_at('origin_map','origin_map_sha256'),'Conflicting module transport aliases') if row['origin_map']
        pair
      else
        [row.fetch('origin_map'),row.fetch('origin_map_sha256')]
      end
    end

    def origin_modules!(path)
      @origin_modules||={}
      return @origin_modules[path] if @origin_modules.key?(path)
      origin=json(path)
      origin_member=->(p) { AtlasParentReceipts.within(File.dirname(path),p) }
      equal(origin.fetch('format'),1,'Unsupported source-origin map')
      equal(files.sha(member(origin_member.call(origin.fetch('merged_sources')))),origin.fetch('merged_sources_sha256'),'Changed original MERGED_SOURCES binding')
      equal(files.sha(member(origin_member.call(origin.fetch('source_hashes')))),origin.fetch('source_hashes_sha256'),'Changed origin-map export binding')
      equal(json(origin_member.call(origin['source_hashes'])),sources,'Source-origin map does not bind exact export')
      registry=json(origin_member.call(origin['merged_sources'])).fetch('sources')
      modules=origin.fetch('modules');archives=origin.fetch('original_sources')
      equal(modules.keys.sort,registry.values.map { |r|r.fetch('module') }.sort,'Incomplete or duplicate source-origin module selection')
      equal(archives.keys.sort,modules.keys.sort,'Incomplete original source archive')
      raise 'Non-injective source-origin map' unless modules.values.uniq.size==modules.size
      registry.each do |source,r|
        mod=r.fetch('module')
        equal(source,mod.tr('.','/')+'.lean','Origin registry module/source mismatch')
        equal(source,r.fetch('source'),'Origin registry source identity differs')
        equal(r.fetch('sha256'),sources.fetch(source),'Origin registry has stale canonical source')
        equal(modules.fetch(mod),r.fetch('original_module'),'Module map disagrees with original source identity')
        archive=archives.fetch(mod)
        equal(archive.fetch('sha256'),r.fetch('original_sha256'),'Original source hash disagrees with registry')
        equal(files.sha(member(origin_member.call(archive.fetch('path')))),r['original_sha256'],'Archived original source changed')
      end
      @origin_modules[path]=modules
    end

    def canonical_original_scope!(scope)
      equal(scope.values_at('manifest','sha256','original_manifest','original_manifest_sha256','original_receipt','previous_mathematical_pass','target_count'),
        [CANONICAL_ORIGINAL_SCOPE,CANONICAL_ORIGINAL_SHA,CANONICAL_ORIGINAL_PATH,CANONICAL_ORIGINAL_SHA,nil,false,11],
        'Canonical original-policy exception has different scope/hash/provenance')
      equal(scope.fetch('original_receipt'),nil,'Canonical original-policy exception has historical receipt')
      equal(scope['original_receipt_sha256'],nil,'Canonical original-policy exception has historical receipt hash')
    end

    def original_policy_view!(row)
      view=row.fetch('original_policy_view','source-origin')
      return view if view=='source-origin'
      equal(view,'canonical-new-policy','Unknown original policy naming view')
      equal(row.fetch('kind'),'source-transported','Canonical original-policy marker on wrong policy kind')
      key='scope-'+Digest::SHA256.hexdigest(CANONICAL_ORIGINAL_SCOPE)[0,24]
      equal(row.fetch('id'),'original-'+key,'Canonical original-policy marker on different policy')
      scopes=json(record.fetch('merged_sources')).fetch('scopes').select { |s|s['manifest']==CANONICAL_ORIGINAL_SCOPE }
      equal(scopes.size,1,'Canonical original-policy scope missing or duplicated')
      canonical_original_scope!(scopes.fetch(0))
      equal(row.fetch('sha256'),CANONICAL_ORIGINAL_SHA,'Canonical original-policy digest differs')
      equal(files.sha(member(row.fetch('manifest'))),CANONICAL_ORIGINAL_SHA,'Canonical original-policy bytes differ')
      view
    end

    def transport_original!(row, policy, declarations, graph)
      path,_hash=origin_pointer(row)
      modules=origin_modules!(path)
      if @current_parent
        equal(json(path).fetch('merged_sources_sha256'),@current_parent[:result].fetch('integration_registry_sha256'),'Origin map is not the parent-verified source registry')
      end
      # The map must be injective also against unchanged/baseline modules.
      seen=graph.values.flat_map { |n|[n.fetch('module'),n['source_module']].compact }.uniq
      raise 'Origin map collides with unchanged graph modules' unless seen.map { |m|modules.fetch(m,m) }.uniq.size==seen.size
      # Validate and retain the entire source-origin map above. Only this exact
      # new policy uses the original canonical metadata instead of back-mapping.
      modules={} if original_policy_view!(row)=='canonical-new-policy'
      mapped=graph.transform_values do |node|
        copy=node.merge('module'=>modules.fetch(node.fetch('module'),node['module']))
        copy['source_module']=modules.fetch(node['source_module'],node['source_module']) if node.key?('source_module')
        copy
      end
      mapped_declarations=declarations.map do |d|
        copy=d.merge('module'=>modules.fetch(d.fetch('module'),d['module']))
        copy['source_module']=modules.fetch(d['source_module'],d['source_module']) if d.key?('source_module')
        copy
      end
      targets=policy.fetch('targets').map do |t|
        mod=t['module'] || t.fetch('source').delete_prefix('.lake/packages/mathlib/').delete_suffix('.lean').tr('/','.')
        {'declaration'=>t.fetch('declaration'),'module'=>mod,'kind'=>t.fetch('kind')}
      end
      raise 'Empty original policy targets' if targets.empty?
      equal(policy.fetch('mode'),'full','Original policy is not full mode')
      equal(policy.fetch('definitions'),true,'Original policy omits complete definitions')
      equal(policy.fetch('allowed_axioms').sort,AtlasContracts::AXIOMS.sort,'Original policy axioms differ')
      names=targets.map { |t|t['declaration'] }
      chosen=mapped_declarations.select { |d|names.include?(d['declaration']) }
      declarations_match!(chosen,targets)
      closure=AtlasVerification.closure(mapped,names).to_a.sort
      # Names and type/value edges were retained exactly; only bound provenance
      # module metadata changed. This is the same canonical dependency slice.
      equal(closure,AtlasVerification.closure(graph,names).to_a.sort,'Origin transport changed graph closure')
      [chosen,mapped.slice(*closure),targets]
    end

    def policy_results!(scope, policies, declarations, graph, used)
      return if policies.empty?
      selected=scope.fetch('policies')
      raise 'Empty or duplicate selected policies' if selected.empty? || selected.uniq!=selected
      expected={}
      selected.each do |id|
        row=policies.fetch(id) { raise "Unknown selected policy #{id}" }
        policy=json(row.fetch('manifest'))
        if row['kind']=='source-transported'
          chosen,sliced,targets=transport_original!(row,policy,declarations,graph)
        else
          targets=policy.fetch('targets');checkpoint!(row['manifest'],targets)
          names=targets.map { |t|t.fetch('declaration') }
          chosen=declarations.select { |d|names.include?(d['declaration']) }
          declarations_match!(chosen,targets)
          closure=AtlasVerification.closure(graph,names).to_a.sort
          sliced=graph.slice(*closure)
        end
        outcome=AtlasVerification.check_policy(policy,chosen,sliced)
        expected[id]={'status'=>'passed','manifest_sha256'=>row.fetch('sha256'),'targets'=>targets.size,
          'dependency_nodes'=>sliced.size,'boundaries'=>JSON.parse(JSON.generate(outcome))}
        if row['kind']=='source-transported'
          _path,hash=origin_pointer(row)
          expected[id][row['module_transport'] ? 'module_transport_sha256' : 'origin_map_sha256']=hash
          expected[id]['original_policy_view']=row['original_policy_view'] if row.key?('original_policy_view')
        end
        used<<id
      end
      raise 'Primary checkpoint omitted from required policies' unless selected.any? { |id|policies[id]['manifest']==scope.fetch('checkpoint') }
      equal(json(scope.fetch('policy_results')),expected,'Required per-policy outcomes differ')
    end

    def parent_process_binding!(check, full:false, cache:false)
      equal(files.sha(member(check.fetch('parent_result'))),check.fetch('parent_result_sha256'),'Original parent proof receipt changed')
      objects=json((record && record['object_bindings']) || 'OBJECT_BINDINGS.json') unless full || cache
      proof=AtlasParentReceipts.validate(files,member(check['parent_result']),sources,normal:!full && !cache,full:full,current_objects:objects)
      equal(proof[:result]['mode'],'cache-current','New whole-cache step requires actual current-cache parent validation') if cache
      equal(proof[:result].fetch('integration_registry_sha256'),@merged_sha,'Parent audit used a different complete source/scope registry') if full && @merged_sha
      adapted=json(check.fetch('record'))
      original=proof[:process].merge('log_sha256'=>proof[:plain_sha256])
      equal(adapted.slice(*original.keys),original,'Derived process changed original fields')
      equal(member(check.fetch('log')),proof[:log_path],'Normal row substitutes original process log')
      binding=adapted.fetch('adaptation').fetch('original_receipt')
      actual=AtlasParentReceipts.within(File.dirname(member(check['record'])),binding.fetch('path'))
      equal(actual,proof[:process_path],'Process adapter points at a different original')
      equal(binding.fetch('sha256'),proof[:result].fetch('process_receipt_sha256'),'Process adapter original digest differs')
      proof
    end

    # Completeness is established by the producer's exact merged inventory,
    # not by a publication editor's potentially shortened POLICIES.json.
    def scope_inventory!(policies,scopes,batches)
      merged_path=record.fetch('merged_sources')
      @merged_sha=files.sha(member(merged_path))
      merged=json(merged_path)
      registered=merged.fetch('scopes')
      paths=registered.map { |r|r.fetch('manifest') }
      raise 'Empty or duplicate registered scope path' if paths.empty? || paths.uniq!=paths
      expected=registered.flat_map do |r|
        key='scope-'+Digest::SHA256.hexdigest(r['manifest'])[0,24]
        original={'id'=>'original-'+key,'kind'=>'source-transported','scope'=>r['manifest'],'manifest'=>r.fetch('original_manifest'),'sha256'=>r.fetch('original_manifest_sha256')}
        if r['manifest']==CANONICAL_ORIGINAL_SCOPE
          canonical_original_scope!(r)
          original['original_policy_view']='canonical-new-policy'
        end
        [{'id'=>'canonical-'+key,'kind'=>'successor','scope'=>r['manifest'],'manifest'=>r['manifest'],'sha256'=>r.fetch('sha256')},
         original]
      end
      equal(policies.keys.sort,expected.map { |r|r['id'] }.sort,'Required merged-inventory policies were omitted or added')
      expected.each do |r|
        p=policies.fetch(r['id'])
        equal(p.values_at('kind','sha256','original_policy_view'),r.values_at('kind','sha256','original_policy_view'),'Policy differs from exact original/successor registry')
      end
      by_id=scopes.to_h { |s|[s.fetch('id'),s] }
      keys=paths.map { |p|'scope-'+Digest::SHA256.hexdigest(p)[0,24] }
      equal(by_id.keys.sort,keys.sort,'Registered full scopes were omitted or added')
      registered.each do |r|
        key='scope-'+Digest::SHA256.hexdigest(r['manifest'])[0,24];s=by_id.fetch(key)
        equal(s.fetch('policies').sort,['canonical-'+key,'original-'+key].sort,'Scope must retain both exact original and successor policies')
        equal(files.sha(member(s.fetch('checkpoint'))),r.fetch('sha256'),'Scope checkpoint differs from registered successor')
        equal(json(s.fetch('roots')).size,r.fetch('target_count'),'Registered scope target count differs')
      end
      return if batches.empty?
      path=record.fetch('batch_registry');@batch_registry_sha=files.sha(member(path));registry=json(path)
      equal(registry.values_at('format','protocol','registration_status'),[1,'atlas-registered-full-audit-batches-v1','registered-parent-reviewed'],'Batch registry is not parent-reviewed')
      equal(registry.fetch('merged_sources').fetch('sha256'),@merged_sha,'Batch registry binds a different merged inventory')
      equal(registry.fetch('scope_inventory'),registered,'Batch registry scope inventory differs')
      equal(registry.fetch('scope_count'),registered.size,'Batch registry scope count differs')
      equal(registry.fetch('required_policies'),expected,'Batch registry omits original/successor policies')
      registered_batches=registry.fetch('batches')
      equal(registered_batches.map { |b|b['id'] }.sort,batches.map { |b|b['id'] }.sort,'Registered extraction batches were omitted or added')
      equal(registered_batches.flat_map { |b|b.fetch('scopes') }.sort,paths.sort,'Every registered scope must occur exactly once')
      registered_batches.each do |b|
        row=batches.find { |s|s['id']==b['id'] }
        equal(files.sha(member(row.fetch('checkpoint'))),b.fetch('sha256'),'Batch checkpoint differs from registered union')
        actual=scopes.select { |s|s['batch']==b['id'] }.map { |s|s['id'] }.sort
        equal(actual,b['scopes'].map { |p|'scope-'+Digest::SHA256.hexdigest(p)[0,24] }.sort,'Batch changed registered member scopes')
      end
    end

    def batch_scope_binding!(scope,parent,policies)
      evidence=parent.fetch(:batch_evidence)
      original=evidence.fetch('scopes').find { |s|s['id']==scope['id'] } or raise 'Scope absent from original batch evidence'
      equal(scope.fetch('policies'),original.fetch('policies'),'Scope policy selection differs from original batch evidence')
      equal(scope.fetch('batch'),original.fetch('batch'),'Scope batch differs from original batch evidence')
      base=File.dirname(parent[:result_path])
      %w[roots checkpoint result policy_results dependency_slice].each do |field|
        path=AtlasParentReceipts.within(base,original.fetch(field))
        equal(files.sha(member(scope.fetch(field))),files.sha(path),"Scoped artifact differs from original parent: #{field}")
        AtlasParentReceipts.guarded(files,path,parent[:guarded_bindings])
      end
      raw_policies_path=AtlasParentReceipts.within(base,evidence.fetch('policy_inventory'))
      AtlasParentReceipts.guarded(files,raw_policies_path,parent[:guarded_bindings])
      raw_policies=files.json(raw_policies_path).fetch('entries').to_h { |p|[p.fetch('id'),p] }
      scope['policies'].each do |id|
        p=policies.fetch(id);raw=raw_policies.fetch(id)
        equal(p.values_at('kind','sha256','original_policy_view'),raw.values_at('kind','sha256','original_policy_view'),'Adapted policy differs from original batch evidence')
        path=AtlasParentReceipts.within(base,raw.fetch('manifest'))
        equal(files.sha(member(p.fetch('manifest'))),files.sha(path),'Original policy bytes differ')
        AtlasParentReceipts.guarded(files,path,parent[:guarded_bindings])
        next unless raw['kind']=='source-transported'
        raw_path,raw_hash=origin_pointer(raw);path,hash=origin_pointer(p)
        equal(hash,raw_hash,'Adapted origin-map hash differs')
        equal(files.sha(member(path)),files.sha(AtlasParentReceipts.within(base,raw_path)),'Adapted origin-map bytes differ')
        AtlasParentReceipts.guarded(files,AtlasParentReceipts.within(base,raw_path),parent[:guarded_bindings])
      end
    end

    def slice_binding!(scope,result,parent,closure,batch_id)
      equal(json(scope.fetch('dependency_slice')),closure,'Scope slice is not exact root dependency closure')
      equal(result.fetch('batch'),batch_id,'Scope receipt names wrong batch')
      equal(result.fetch('batch_process_sha256'),parent[:result].fetch('process_receipt_sha256'),'Scope receipt names wrong original successful process')
      path=scope.fetch('dependency_slice')
      equal(result.fetch('dependency_slice_sha256'),files.sha(member(path)),'Scope receipt slice binding differs')
      if path.end_with?('.gz')
        hash=@bundle.fetch('uncompressed_hashes').fetch(path.delete_suffix('.gz'))
        digest=Digest::SHA256.new;each_line(path) { |line|digest.update(line) }
        equal(digest.hexdigest,hash,'Scope slice uncompressed binding differs')
        equal(result['dependency_slice_uncompressed_sha256'],hash,'Scope result plain slice binding differs') if result.key?('dependency_slice_uncompressed_sha256')
      end
    end

    def normal_proof!(check)
      proof=parent_process_binding!(check)
      equal(check.fetch('sources'),[proof[:result].fetch('source')],'Normal row credits sources not checked by parent')
      proof
    end

    def cache_step!(step)
      if step.fetch('name')=='cache-hashes'
        proof=parent_process_binding!(step,cache:true)
        objects=proof.fetch(:cache_binding).fetch(:objects);artifacts=proof[:cache_binding].fetch(:artifacts)
        equal(json('OBJECT_BINDINGS.json'),objects,'Whole-cache object alias differs from original current validation')
        equal(json('CACHE_SOURCE_HASHES.json'),sources,'Whole-cache compatible-source alias differs')
        %w[CACHE_ARTIFACTS.json CACHE_ARTIFACTS_AFTER.json].each { |p|equal(json(p),artifacts,'Whole-cache artifact alias differs from current validation') }
        if index && index['source_update']
          dir=index['source_update'].fetch('proof_evidence').fetch('directory')
          additions=files.json(dir+'/ADDITIONS.json')
          path=AtlasParentReceipts.within(dir,additions.fetch('object_bindings','OBJECT_BINDINGS.json'))
          equal(files.json(path),objects,'Addition normal proofs use a different final object inventory')
        end
        proof
      else
        source={'root-elaboration'=>'Atlas.lean','audit-root-elaboration'=>'Atlas/Audit.lean'}.fetch(step['name'])
        proof=normal_proof!(step.merge('sources'=>[source]))
        equal(proof[:result]['mode'],'root','Fresh root step requires original root-mode success')
      end
    end

    def history!
      update = index.fetch('source_update')
      equal(update.fetch('format'), 1, 'Unsupported source-update schema')
      equal(files.sha(update.fetch('previous_index')), BASELINE_INDEX, 'Changed published v1.2 baseline index')
      equal(files.sha(update.fetch('previous_manifest')), BASELINE_MANIFEST, 'Changed published v1.2 baseline manifest')
      @previous = files.json(update['previous_index'])
      manifest = files.json(update['previous_manifest'])
      equal(manifest.fetch('files').fetch('verification/current.json'), BASELINE_INDEX, 'Baseline manifest/index mismatch')
      %w[contracts prior_accepted_release prior_accepted_release_sha256 dated_nanoda deferred_contracts].each do |key|
        equal(index.fetch(key), previous.fetch(key), "Historical binding changed: #{key}")
      end
      %w[verification/existence/registry.json verification/release-candidate/V1_BASELINE.json].each do |path|
        equal(files.sha(path), manifest.fetch('files').fetch(path), "Historical file changed: #{path}")
      end
      old = previous.fetch('supplemental_cache_audit')
      raise 'Old audit cannot be relabelled as a successor' if directory == old.fetch('directory')
      files.validate_bundle(old.fetch('directory'), old.fetch('bundle_sha256'))
      @previous_sources = files.json(old['directory']+'/SOURCE_HASHES.json')
      @previous_roots = files.json(old['directory']+'/roots.json')
      raise 'Previously audited roots removed or changed' unless (@previous_roots-roots).empty?
      raise 'Previously exported sources removed' unless (@previous_sources.keys-sources.keys).empty?
      %w[lean-toolchain lakefile.toml lake-manifest.json].each do |p|
        equal(sources.fetch(p), @previous_sources.fetch(p), "Dependency/package pin changed: #{p}")
      end
      @previous_sources.each do |p,h|
        next unless p.end_with?('.lean') && !%w[Atlas.lean Atlas/Audit.lean].include?(p)
        equal(sources.fetch(p), h, "Published mathematical source changed: #{p}")
      end
      equal(update.fetch('purpose'), 'prepare-editable-v1.2-update', 'Wrong source-update purpose')
      raise 'Missing source-update owner instruction' unless update.fetch('owner_decision').is_a?(String) && !update['owner_decision'].strip.empty?
      @update_date = Date.iso8601(update.fetch('authorized_on'))
      raise 'Source update predates its owner instruction' unless @update_date>=Date.new(2026,10,30)
    end

    def validate!
      history!
      ptr = @pointer
      equal(ptr.fetch('format'), @whole ? 2 : 1, 'Unsupported exact-export evidence pointer')
      @bundle = files.validate_bundle(directory, ptr.fetch('bundle_sha256'))
      @bundle.fetch('uncompressed_hashes').each do |path, expected_sha|
        digest = Digest::SHA256.new
        each_line(path+'.gz') { |line| digest.update(line) }
        equal(digest.hexdigest, expected_sha, 'Changed uncompressed successor artifact')
      end
      @record = json(@whole ? 'CACHE_AUDIT.json' : 'ADDITIONS.json')
      equal(record.values_at('format','status'), @whole ? [2,'passed-source-bound-cache-audit'] : [1,'passed-source-bound-additions'], 'Wrong successor audit status')
      %w[fresh_project_rebuild independent_replay].each { |key| equal(record.fetch(key), false, 'Supplemental audit cannot be promoted to acceptance') }
      equal(record.fetch('sources_unchanged'), true, 'Successor audit inputs changed')
      DateTime.iso8601(record.fetch('finished_utc'))
      %w[SOURCE_HASHES.json SOURCE_HASHES_AFTER.json].each do |p|
        equal(json(p), sources, 'Successor/cache sources do not equal exact export')
      end
      audit_roots = json('roots.json')
      raise 'Invalid evidence roots' unless !audit_roots.empty? && audit_roots.map { |r| r.fetch('declaration') }.uniq.size==audit_roots.size && audit_roots==audit_roots.sort_by { |r| r['declaration'] }
      if @whole
        equal(audit_roots, roots, 'Successor audit target selection changed')
      else
        raise 'New public references missing from addition policies' unless (identities(roots)-identities(@previous_roots)-identities(audit_roots)).empty?
        audit_roots.each do |r|
          raise 'Noncanonical addition policy root' unless sources.key?(r.fetch('module').tr('.', '/')+'.lean') && %w[any theorem definition].include?(r.fetch('kind'))
        end
      end
      equal(record.fetch('roots'), audit_roots.size, 'Wrong successor root count')
      equal(record.fetch('allowed_axioms').sort, AtlasContracts::AXIOMS.sort, 'Unapproved successor axioms')
      revisions = files.json('lake-manifest.json').fetch('packages').to_h { |p| [p.fetch('name'),p.fetch('rev')] }
      equal(record.fetch('dependency_revisions'), revisions, 'Successor dependency pins differ')
      steps = []
      if @whole
        equal(record.fetch('cache_artifacts_unchanged'), true, 'Successor cache changed')
        equal(json('CACHE_SOURCE_HASHES.json'), sources, 'Cache does not bind exact exported bytes')
        %w[CACHE_ARTIFACTS.json CACHE_ARTIFACTS_AFTER.json].each { |p| member(p) }
        AtlasReleaseEvidence.cache_artifacts!(files,directory,sources)
        steps = record.fetch('steps')
        equal(steps.map { |s| s.fetch('name') }, %w[cache-hashes root-elaboration audit-root-elaboration], 'Missing cache/root validation steps')
      end
      processes = steps.map { |s| cache_step!(s);process!(s) }
      checked = []
      normal = @whole ? [] : record.fetch('normal_proof_checks')
      normal_ids = normal.map { |r| r.fetch('id') }
      raise 'Duplicate normal proof id' unless normal_ids.uniq==normal_ids
      @merged_sha=files.sha(member(record.fetch('merged_sources'))) unless @whole
      normal.each do |check|
        paths = check.fetch('sources')
        raise 'Empty or invalid normal proof source selection' unless paths.is_a?(Array) && !paths.empty? && paths.uniq==paths && paths.all? { |p| sources.key?(p) && p.end_with?('.lean') }
        equal(check.fetch('fresh_source_check'), true, 'Normal proof check must re-elaborate source')
        normal_proof!(check)
        processes << process!(check)
        checked.concat(paths)
      end
      changed = (sources.keys-@previous_sources.keys).grep(/\.lean\z/)
      raise "Missing normal proof checks: #{(changed-checked).join(', ')}" unless @whole || (changed-checked).empty?
      scopes = record.fetch('scopes')
      raise 'Missing full audit scopes' if scopes.empty?
      ids = scopes.map { |s| s.fetch('id') }
      raise 'Duplicate full audit scope' unless ids.uniq==ids
      batches=record.fetch('batches',[])
      batch_ids=batches.map { |b|b.fetch('id') }
      raise 'Duplicate batch id' unless batch_ids.uniq==batch_ids
      raise 'Batch/policy inventory missing' if !batches.empty? && !record['policy_inventory']
      policies=policy_inventory!;used_policies=[]
      scope_inventory!(policies,scopes,batches) unless @whole
      selected=[];nodes=0;extractions=[];scope_facts={}
      grouped=scopes.group_by { |s|s['batch'] ? ['batch',s['batch']] : ['single',s.fetch('id')] }
      equal(grouped.keys.select { |k|k[0]=='batch' }.map(&:last).sort,batch_ids.sort,'Unused or missing extraction batch')
      grouped.each do |key, members|
        row=key[0]=='batch' ? batches.find { |b|b['id']==key[1] } : members.fetch(0)
        batch_targets,declarations,graph,process,parent=extraction!(row)
        if key[0]=='batch'
          equal(parent[:result]['mode'],'audit-batch','Grouped extraction lacks a registered batch parent')
          equal(parent.fetch(:batch_evidence).fetch('registry_sha256'),@batch_registry_sha,'Parent batch used a different full registry') unless @whole
          equal(parent[:batch_evidence].fetch('scopes').map { |s|s['id'] }.sort,members.map { |s|s['id'] }.sort,'Scope omitted from original successful batch')
        end
        raise 'Foreign extraction roots' unless (identities(batch_targets)-identities(audit_roots)).empty?
        if key[0]=='batch'
          %w[source_hashes source_hashes_after].each { |field|equal(json(row.fetch(field)),sources,'Batch source binding differs from exact export') }
        end
        processes<<process;extractions<<row;logs<<member(row.fetch('log'));nodes+=graph.size
        covered=[]
        members.each do |scope|
          scope_roots=json(scope.fetch('roots'))
          raise 'Empty, duplicate or foreign scope roots' unless !scope_roots.empty? && scope_roots.map { |r|r.fetch('declaration') }.uniq.size==scope_roots.size && (identities(scope_roots)-identities(batch_targets)).empty?
          names=scope_roots.map { |r|r.fetch('declaration') }
          chosen=declarations.select { |d|names.include?(d['declaration']) }
          declarations_match!(chosen,scope_roots)
          closure=AtlasVerification.closure(graph,names).to_a.sort
          slice=graph.slice(*closure)
          checkpoint=checkpoint!(scope.fetch('checkpoint'),scope_roots)
          result=result!(scope,checkpoint,chosen,slice)
          if key[0]=='batch'
            batch_scope_binding!(scope,parent,policies)
            slice_binding!(scope,result,parent,closure,row.fetch('id'))
          end
          policy_results!(scope,policies,chosen,slice,used_policies)
          scope_facts[member(scope.fetch('result'))]={scope:scope,extraction:row,roots:scope_roots,declarations:chosen}
          covered.concat(scope_roots);selected.concat(scope_roots)
        end
        equal(identities(covered),identities(batch_targets),'Scoped receipts omit batch targets')
      end
      equal(used_policies.uniq.sort,policies.keys.sort,'Required original/successor policies were omitted')
      equal(identities(selected),identities(audit_roots),'Full audit scopes omit selected roots')
      records=(steps+normal+extractions).map { |s|s.fetch('record') }
      raise 'One process receipt reused without an explicit shared batch' unless records.uniq==records
      %w[record log declarations dependencies].each do |field|
        paths=extractions.map { |s|s.fetch(field) }
        raise "Reused extraction artifact #{field}" unless paths.uniq==paths
      end
      raise 'Reused scoped result' unless scopes.map { |s|s.fetch('result') }.uniq.size==scopes.size
      unless @whole
        entries=AtlasReleaseEvidence.checkpoints(files,index)
        if !entries.empty? && Date.iso8601(files.json(AtlasReleaseEvidence::CHECKPOINTS).fetch('as_of'))<DateTime.iso8601(record.fetch('finished_utc')).to_date
          raise 'Checkpoint date precedes its new evidence'
        end
        evidence=entries.empty? ? {} : files.json(AtlasReleaseEvidence::CHECKPOINTS).fetch('evidence')
        entries.each do |entry|
          entry.fetch('selected_refs').each do |ref|
            bound=evidence.fetch(ref.fetch('evidence'))
            fact=scope_facts.fetch(bound.fetch('full_audit')) { raise 'Checkpoint full audit is outside required additions evidence' }
            selected_ref=AtlasReleaseEvidence.reference(ref,files)
            raise 'Checkpoint evidence omits selected declarations' unless identities(fact[:roots]).include?(selected_ref.slice('declaration','module'))
            declaration=fact[:declarations].find { |d|d['declaration']==ref['declaration'] }
            declarations_match!([declaration],[selected_ref.merge('kind'=>ref.fetch('kind'))])
            equal(bound.fetch('manifest'),member(fact[:scope].fetch('checkpoint')),'Checkpoint points at unrelated policy manifest')
            equal(bound.fetch('source_binding').fetch('path'),member('SOURCE_HASHES.json'),'Checkpoint source binding differs')
            equal(bound.fetch('compiled_statements').fetch('path'),member(fact[:extraction].fetch('log')),'Checkpoint statement binding differs')
            raise 'Checkpoint evidence omits normal source checks' unless @previous_sources.key?(ref['source']) || normal.any? { |s|s.fetch('sources').include?(ref['source']) }
          end
        end
      end
      # Count each extraction once, even when its graph supports many scopes.
      @summary = {roots: audit_roots.size, scopes: scopes.size, dependency_node_occurrences: nodes,
        finished_utc: record.fetch('finished_utc'), peak_owned_rss_and_swap: processes.map { |p| p.fetch('peak_owned_rss_and_swap',0) }.max}
      self
    end
  end

  # Renderer entry point: bundle/member hashing applies even outside the gate.
  # The gate additionally validates complete graph closure, policies and history.
  def self.statement_logs(files, index)
    ptr = index.fetch('supplemental_cache_audit')
    dir = ptr.fetch('directory')
    bundle = files.validate_bundle(dir, ptr.fetch('bundle_sha256'))
    logs = if ptr['format']==2
      audit=files.json(dir+'/CACHE_AUDIT.json')
      (audit.fetch('batches',[])+audit.fetch('scopes').reject { |s|s['batch'] }).map { |s|s.fetch('log') }
    else
      ['full-dependency-extraction.log.gz']
    end
    raise 'Empty compiled-statement selection' if logs.empty?
    logs.map do |p|
      raise 'Unbound compiled-statement log' unless bundle.fetch('files').key?(p)
      files.path(dir+'/'+p)
      dir+'/'+p
    end
  end

  def self.statements(files, index, wanted)
    statements = {}
    statement_logs(files, index).each do |path|
      full = files.path(path)
      io = path.end_with?('.gz') ? Zlib::GzipReader.open(full) : File.open(full)
      begin
        name = nil; lines = []
        flush = lambda do
          if name && !lines.empty?
            text = lines.join
            raise "Conflicting compiled signature: #{name}" if statements.key?(name) && statements[name][:text]!=text
            statements[name] ||= {text: text, path: path}
          end
        end
        io.each_line do |line|
          if line.match?(/\A(?:STATEMENT|DEFINITION|SHARED EXTRACTION|AXIOMS)\b/)
            flush.call; lines = []
            n = line[/\ASTATEMENT (\S+) SOURCE /,1]
            name = wanted.include?(n) ? n : nil
          elsif name
            lines << line
          end
        end
        flush.call
      ensure
        io.close
      end
    end
    missing = wanted.to_a-statements.keys
    raise "Missing compiled signatures: #{missing.join(', ')}" unless missing.empty?
    statements
  end
end
