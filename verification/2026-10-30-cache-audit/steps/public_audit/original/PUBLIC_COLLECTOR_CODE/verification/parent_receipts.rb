# Read-only validation of the authoritative verify.rb/monitor.rb receipts.
# This code runs no verifier, policy audit, compiler, Git command or subprocess.
require 'json'
require 'digest'
require 'zlib'
require 'date'

module AtlasParentReceipts
  AXIOMS=%w[propext Classical.choice Quot.sound].freeze
  STATUSES={'build'=>'passed-fresh-canonical-proof-check','root'=>'passed-fresh-canonical-proof-check',
    'audit'=>'passed-full-canonical-dependency-audit','audit-public'=>'passed-full-canonical-dependency-audit',
    'audit-batch'=>'passed-full-canonical-batch-audit',
    'cache-hashes'=>'passed-baseline-trace-hash-check','cache-current'=>'passed-current-cache-integrity'}.freeze
  FULL_MODES=%w[audit audit-batch audit-public].freeze
  PINS=%w[lean-toolchain lakefile.toml lake-manifest.json].freeze
  OBJECT_FIELDS=%w[source source_sha256 object object_sha256 basis evidence].freeze
  CACHE_PAYLOADS=%w[SOURCE_HASHES.json SOURCE_HASHES_AFTER.json CACHE_SOURCE_HASHES.json
    CACHE_ARTIFACTS.json CACHE_ARTIFACTS_AFTER.json OBJECT_BINDINGS.json
    ORIGINAL_CACHE_SOURCE_HASHES.json ORIGINAL_CACHE_ENVIRONMENT.json COMPILED_SOURCE_HASHES.json
    SOURCE_COMPATIBILITY.json OBJECT_ORIGINS.json IMPORTED_OBJECT_EDGES.json
    PACKAGES_BEFORE.json PACKAGES_AFTER.json PROVENANCE.json INPUT_BINDINGS.json].freeze
  CACHE_FALSE_FLAGS=%w[fresh_whole_project_rebuild fresh_project_rebuild independent_replay
    new_proof_build new_full_dependency_audit new_lake_hash_evaluation_performed].freeze
  OPTIONS=%w[-M8704 -Dpp.unicode.fun=true -DrelaxedAutoImplicit=false -Dweak.linter.mathlibStandardSet=true -DmaxSynthPendingDepth=3].freeze
  def self.equal(a,b,message)
    raise message unless a==b
  end
  def self.hash!(value)
    raise 'Invalid parent artifact hash' unless value.is_a?(String) && value.match?(/\A[0-9a-f]{64}\z/)
  end
  def self.bound(files,path,hash)
    hash!(hash);equal(files.sha(path),hash,"Changed original parent artifact: #{path}")
  end
  def self.within(directory,name)
    raise 'Nonportable original receipt member' unless name.is_a?(String) && !name.empty? && !name.start_with?('/') && name.split('/').none? { |p|p.empty? || %w[. ..].include?(p) }
    directory=='.' ? name : directory+'/'+name
  end
  # Hash decoded bytes in bounded chunks, including the final unterminated
  # line. Never materialize the full graph or normalize its JSON/whitespace.
  def self.gzip_facts(files,path)
    digest=Digest::SHA256.new;bytes=0;lines=0;last=nil
    File.open(files.path(path),'rb') do |raw|
      gzip=Zlib::GzipReader.new(raw)
      begin
        while (chunk=gzip.read(1024*1024))
          break if chunk.empty?
          digest.update(chunk);bytes+=chunk.bytesize;lines+=chunk.count("\n");last=chunk.getbyte(-1)
        end
        raise 'Trailing or concatenated gzip payload' unless gzip.unused.to_s.empty? && raw.eof?
      ensure
        gzip.close
      end
    end
    lines+=1 if bytes>0 && last!=10
    {sha256:digest.hexdigest,bytes:bytes,lines:lines}
  end
  def self.graph_representation(files,result_path,result)
    base=File.dirname(result_path)
    plain=within(base,'dependencies.jsonl');compressed=within(base,'dependencies.jsonl.gz')
    bound(files,compressed,result.fetch('dependency_log_compressed_sha256'))
    decoded=gzip_facts(files,compressed)
    equal(decoded[:sha256],result.fetch('dependency_log_sha256'),'Parent graph compression differs')
    equal(decoded[:lines],result.fetch('dependency_nodes'),'Parent graph node count differs')
    # A genuinely absent plaintext is portable. An existing, dangling-symlinked,
    # unreadable or changed plaintext is still validated and cannot be ignored.
    local=File.join(files.root,plain)
    present=begin
      File.lstat(local);true
    rescue Errno::ENOENT
      false
    end
    if present
      equal(Digest::SHA256.file(files.path(plain)).hexdigest,result['dependency_log_sha256'],"Changed original parent artifact: #{plain}")
    end
    {plain_path:plain,compressed_path:compressed,plain_sha256:decoded[:sha256],
      compressed_sha256:result['dependency_log_compressed_sha256'],plain_bytes:decoded[:bytes],
      compressed_bytes:File.size(files.path(compressed)),lines:decoded[:lines],plaintext_present:present}
  end
  # The parent's final immutable-input map may retain absolute producer paths.
  # It is evidence, never a path to open on the replay machine. Match bytes only.
  def self.guarded(files,path,bindings)
    return if bindings.value?(files.sha(path))
    # Parent may compress an already-bound graph in its final guarded phase.
    # The RESULT binds compressed bytes; the guard must bind exact plain bytes.
    if path.end_with?('.gz')
      return if bindings.value?(gzip_facts(files,path).fetch(:sha256))
    end
    raise "Artifact outside original final guard: #{path}"
  end
  # Portable validation of recorded observations from the reviewed host.
  # Never inspect the replay machine's /proc or infer an unreadable root namespace.
  def self.cache_host_visibility!(contract,result,process,observed,final)
    equal(contract.fetch('host_visibility_helper_sha256'),result.fetch('cache_contract_builder_sha256'),
      'Cache host observer is not the archived contract builder')
    guard=contract.fetch('parent_guard')
    anchor={'method'=>'parent-reviewed-kde-session-chain-v1','chain'=>[
      {'pid'=>1450,'comm'=>'plasmashell','uid'=>1000,'ppid'=>1140,'starttime'=>'1269','nspid'=>[1450]},
      {'pid'=>1140,'comm'=>'systemd','uid'=>1000,'ppid'=>1,'starttime'=>'804','nspid'=>[1140]},
      {'pid'=>1,'comm'=>'systemd','uid'=>0,'ppid'=>0,'starttime'=>'9','nspid'=>[1]}],
      'namespace_source_pid'=>1450,'pid_namespace'=>'pid:[4026531836]',
      'unreadable_namespace_pids_not_observed'=>[1140,1]}
    [guard,observed,final].each do |record|
      equal(record.fetch('host_visibility_anchor'),anchor,'Recorded reviewed host visibility anchor differs')
    end
    equal(guard.fetch('host_pid_namespace'),anchor['pid_namespace'],'Contract namespace differs from readable reviewed anchor')
    parent=guard.fetch('supervisor_pid');child=process.fetch('pid')
    raise 'Invalid observed cache process identities' unless [parent,child].all? { |pid|pid.is_a?(Integer) && pid>1 && ![1450,1140].include?(pid) } && parent!=child
    [[observed,child],[final,parent]].each do |record,pid|
      equal(record.fetch('host_observer'),{'pid'=>pid,'uid'=>1000,'nspid'=>[pid],'pid_namespace'=>anchor['pid_namespace']},
        'Recorded cache observer PID/UID/namespace depth differs')
    end
  end
  def self.cache_current(files,result_path,result,process,sources,bindings)
    base=File.dirname(result_path);member=->(p) { within(base,p) }
    equal(result.fetch('cache_binding'),'cache/CACHE_BINDING.json','Unexpected current-cache child path')
    path=member.call(result['cache_binding']);bound(files,path,result.fetch('cache_binding_sha256'));guarded(files,path,bindings)
    child=files.json(path);cache_dir=File.dirname(path)
    equal(child.values_at('format','status'),[1,'validated-current-cache-integrity-child-result'],'Current-cache child did not validate')
    %w[sources_unchanged cache_artifacts_unchanged original_receipts_unchanged current_cache_integrity_validation_performed].each do |f|
      equal(child.fetch(f),true,"Child cache #{f} missing");equal(result.fetch(f),true,"Parent cache #{f} missing")
    end
    equal(result.fetch('source_to_object_bindings_verified'),true,'Parent cache source/object validation missing')
    equal(child.fetch('parent_monitor_finalization_required'),true,'Cache child finalization contract differs')
    CACHE_FALSE_FLAGS.each do |f|
      equal(child.fetch(f),false,'Cache child cannot become proof/audit/replay evidence')
      equal(result.fetch(f),false,'Cache parent cannot become proof/audit/replay evidence')
    end
    equal(result.fetch('source_binding_semantics'),child.fetch('source_binding_semantics'),'Cache source semantics changed')
    equal(child.fetch('original_compiled_source_map'),'COMPILED_SOURCE_HASHES.json','Missing original compiled-source map')
    equal(child.fetch('original_baseline_cache_source_map'),'ORIGINAL_CACHE_SOURCE_HASHES.json','Missing original baseline source map')
    raise 'Missing historical cache provenance limit' if child.fetch('historical_trace_hash_binding_limit').empty?
    inventory=child.fetch('files')
    raise 'Incomplete current-cache payload' unless (CACHE_PAYLOADS-inventory.keys).empty?
    inventory.each do |p,h|
      artifact=within(cache_dir,p);bound(files,artifact,h);guarded(files,artifact,bindings)
    end
    document=->(p) { files.json(within(cache_dir,p)) }
    %w[SOURCE_HASHES.json SOURCE_HASHES_AFTER.json CACHE_SOURCE_HASHES.json].each do |p|
      equal(document.call(p),sources,'Current cache does not bind the full current snapshot')
    end
    %w[object_bindings cache_artifacts cache_artifacts_after].zip(%w[OBJECT_BINDINGS.json CACHE_ARTIFACTS.json CACHE_ARTIFACTS_AFTER.json]).each do |field,p|
      equal(result.fetch(field),'cache/'+p,'Unexpected current cache artifact path')
      equal(result.fetch(field+'_sha256'),inventory.fetch(p),'Parent/child current cache artifact hash differs')
    end
    objects=document.call('OBJECT_BINDINGS.json');artifacts=document.call('CACHE_ARTIFACTS.json')
    equal(document.call('CACHE_ARTIFACTS_AFTER.json'),artifacts,'Current cache objects changed')
    lean=sources.keys.grep(/\.lean\z/).sort
    equal(objects.keys.sort,lean.map { |p|p.delete_suffix('.lean').tr('/','.') }.sort,'Current cache object selection differs')
    expected=objects.to_h do |mod,row|
      source=mod.tr('.','/')+'.lean';object='.lake/build/lib/lean/'+mod.tr('.','/')+'.olean'
      equal(row.fetch('source'),source,'Cache object/source module differs')
      equal(row.fetch('source_sha256'),sources.fetch(source),'Cache compatible source differs')
      equal(row.fetch('object'),object,'Cache object path differs');hash!(row.fetch('object_sha256'))
      row.fetch('evidence')
      raise 'Unknown cache object origin' unless %w[fresh-canonical-proof-check validated-published-baseline-cache].include?(row.fetch('basis'))
      [object,row['object_sha256']]
    end
    equal(artifacts,expected,'Current cache artifact hashes differ from object bindings')
    fresh=objects.select { |_m,r|r['basis']=='fresh-canonical-proof-check' }.keys
    roots=%w[Atlas Atlas.Audit];raise 'Current cache lacks fresh roots' unless (roots-fresh).empty?
    baseline=objects.keys-fresh
    counts={'baseline_objects'=>baseline.size,'new_normal_proofs'=>(fresh-roots).size,'fresh_root_elaborations'=>roots.size,
      'objects'=>objects.size,'source_and_pin_entries'=>sources.size}
    equal(child.fetch('counts'),counts,'Child cache counts differ');equal(result.fetch('cache_counts'),counts,'Parent cache counts differ')
    compiled=document.call('COMPILED_SOURCE_HASHES.json');original=document.call('ORIGINAL_CACHE_SOURCE_HASHES.json')
    equal(compiled.keys.sort,lean,'Incomplete actual compiled-source inventory')
    equal(original.keys.sort,(baseline.map { |m|objects[m]['source'] }+PINS).sort,'Original baseline source selection differs')
    original_environment=document.call('ORIGINAL_CACHE_ENVIRONMENT.json')
    equal(original_environment.fetch('pins'),original.slice(*PINS),'Original cache environment/pin map differs')
    equal(original_environment.fetch('dependency_revisions'),result.fetch('dependency_revisions'),'Original cache dependency revisions differ')
    origins=document.call('OBJECT_ORIGINS.json');equal(origins.keys.sort,objects.keys.sort,'Incomplete per-object cache provenance')
    compatibility=document.call('SOURCE_COMPATIBILITY.json')
    objects.each do |mod,row|
      source=row['source'];origin=origins.fetch(mod);hash!(compiled.fetch(source))
      equal(origin.values_at('basis','compiled_source_sha256','current_compatible_source_sha256','object_sha256'),
        [row['basis'],compiled[source],sources[source],row['object_sha256']],'Original/compatible object provenance differs')
      if fresh.include?(mod)
        equal(compiled[source],sources[source],'Fresh object compiled source differs')
      else
        equal(compiled[source],original.fetch(source),'Original baseline compiled source relabelled')
        c=compatibility.fetch(source)
        equal(c.values_at('original_compiled_source_sha256','current_source_sha256'),[compiled[source],sources[source]],'Baseline source compatibility differs')
      end
    end
    provenance=document.call('PROVENANCE.json')
    provenance.each_value { |p|equal(inventory.fetch(p.fetch('member')),p.fetch('sha256'),'Original cache provenance member differs') }
    child.fetch('anchors').each_value { |p|equal(inventory.fetch(p.fetch('member')),p.fetch('sha256'),'Cache anchor member differs') }
    packages=document.call('PACKAGES_BEFORE.json');equal(document.call('PACKAGES_AFTER.json'),packages,'Cache dependency packages changed')
    revisions=result.fetch('dependency_revisions').to_h { |n,h|['.lake/packages/'+n,h] }
    equal(packages.transform_values { |v|v.fetch('revision') },revisions,'Current cache package revisions differ')
    raise 'Current cache package cleanliness missing' unless packages.values.all? { |v|v['working_tree_clean']==true && v['untracked_nonignored_clean']==true }
    contract_path=member.call(result.fetch('cache_contract'));bound(files,contract_path,result.fetch('cache_contract_sha256'));guarded(files,contract_path,bindings)
    contract=files.json(contract_path)
    equal(result['cache_contract'],'CACHE_CONTRACT.json','Unexpected cache contract path')
    equal(child.fetch('parent_contract_sha256'),result['cache_contract_sha256'],'Cache child used a different contract')
    equal(child.fetch('tool_sha256'),result.fetch('cache_validator_sha256'),'Cache validator identity differs')
    equal(contract.fetch('validator_sha256'),result['cache_validator_sha256'],'Cache contract validator differs')
    equal(result.fetch('current_object_index_sha256'),contract.fetch('anchors').fetch('OBJECT_BINDINGS').fetch('sha256'),'Parent current object anchor differs')
    equal(child.fetch('anchors').keys.sort,contract['anchors'].keys.sort,'Cache anchor selection differs')
    contract['anchors'].each { |name,p|equal(child['anchors'][name].fetch('sha256'),p.fetch('sha256'),'Original cache anchor hash differs') }
    {'current-cache-validation.rb'=>'cache_validator_sha256','cache_current_support.rb'=>'cache_support_sha256',
      'cache-contract-builder.rb'=>'cache_contract_builder_sha256'}.each do |p,key|
      bound(files,member.call(p),result.fetch(key));guarded(files,member.call(p),bindings)
    end
    command=process.fetch('command')
    equal(command.drop(1),[contract.fetch('task')+'/current-cache-validation.rb','--contract',contract.fetch('parent_run')+'/CACHE_CONTRACT.json',
      '--out',contract['parent_run']+'/cache'],'Actual current-cache process command differs')
    equal(process.fetch('cwd'),result.fetch('candidate'),'Actual cache working directory differs')
    equal(process.fetch('environment').fetch('ATLAS_CACHE_CONTRACT_SHA256'),result['cache_contract_sha256'],'Actual cache process contract differs')
    guard=contract.fetch('parent_guard');lease=process.fetch('inherited_held_lease');observed=child.fetch('inherited_held_lease')
    equal(guard.values_at('owned_rss_cap_bytes','minimum_available_bytes','combined_worker_ram_fraction','max_lean_workers','allocation_mib'),
      [9*1024**3,1024**3,[2,3],4,8704],'Current-cache guard limits differ')
    equal(lease.values_at('device','inode','owner_pid','parent_owned'),guard.values_at('lease_device','lease_inode','supervisor_pid')+[true],'Original process lease differs')
    equal(observed.values_at('supervisor_pid','supervisor_starttime','host_pid_namespace','inherited_fd','lease_device','lease_inode'),
      guard.values_at('supervisor_pid','supervisor_starttime','host_pid_namespace')+[lease.fetch('descriptor')]+guard.values_at('lease_device','lease_inode'),'Original child lease/host evidence differs')
    equal(process['environment'].fetch('ATLAS_CACHE_LEASE_FD'),lease['descriptor'].to_s,'Actual inherited lease descriptor differs')
    final=result.fetch('cache_final_guard');equal(final.fetch('status'),'passed','Final parent cache guard did not pass')
    equal(final.values_at('supervisor_pid','held_lease_descriptor','host_pid_namespace'),[guard['supervisor_pid'],lease['descriptor'],guard['host_pid_namespace']],'Final cache guard identity differs')
    cache_host_visibility!(contract,result,process,observed,final)
    mem=final.fetch('memory');workers=final.fetch('workers')
    raise 'Final current-cache resource guard failed' unless mem.fetch('MemAvailable')>=1024**3 && final.fetch('supervisor_rss')<9*1024**3 &&
      workers.fetch('combined_rss')<mem.fetch('MemTotal')*2/3 && workers.fetch('total_lean')<=4
    times=[process.fetch('started_utc'),child.fetch('started_utc'),child.fetch('finished_utc'),process.fetch('finished_utc')].map { |t|DateTime.iso8601(t) }
    raise 'Cache child chronology differs from monitored process' unless times.each_cons(2).all? { |a,b|a<=b }
    {path:path,child:child,objects:objects,artifacts:artifacts}
  end
  def self.validate(files,result_path,expected_sources,normal:false,full:false,current_objects:nil)
    directory=File.dirname(result_path)
    member=->(p) { within(directory,p) }
    result=files.json(result_path);mode=result.fetch('mode')
    normal_mode=%w[build root].include?(mode)
    raise 'Wrong normal-proof parent mode' if normal && !%w[build root].include?(mode)
    raise 'Wrong full-audit parent mode' if full && !FULL_MODES.include?(mode)
    equal(result.fetch('status'),STATUSES.fetch(mode) { raise 'Unsupported parent receipt mode' },'Parent verifier did not pass')
    raise 'Parent verifier failed after child success' if result['failure'] || result['ruby_guard_stop']
    %w[canonical_package sources_unchanged].each { |k|equal(result.fetch(k),true,"Parent #{k} not established") }
    %w[fresh_whole_project_rebuild independent_replay].each { |k|equal(result.fetch(k),false,'Parent evidence cannot be promoted') }
    equal(result.fetch('root_integration'),mode=='root','Parent root scope differs')
    sources_path=member.call('SOURCE_HASHES.json')
    bound(files,sources_path,result.fetch('source_hashes_sha256'))
    run_sources=files.json(sources_path)
    raise 'Current object bindings required for normal proof scope' if normal_mode && !current_objects.is_a?(Hash)
    if mode=='build'
      PINS.each { |p|equal(run_sources.fetch(p),expected_sources.fetch(p),'Normal proof pin changed') }
    else
      equal(run_sources,expected_sources,'Parent run does not bind current SOURCE_HASHES')
    end
    if FULL_MODES.include?(mode) || normal_mode || mode=='cache-current'
      equal(result.fetch('final_immutability_verified'),true,'Parent final immutability guard did not pass')
      bound(files,member.call('BOUND_INPUTS.json'),result.fetch('bound_inputs_sha256'))
      bindings=files.json(member.call('BOUND_INPUTS.json'))
      raise 'Empty parent final guard bindings' unless bindings.is_a?(Hash) && !bindings.empty?
      bindings.each_value { |h|hash!(h) }
      guarded(files,sources_path,bindings)
      if FULL_MODES.include?(mode) || mode=='cache-current'
        after_path=member.call('SOURCE_HASHES_AFTER.json')
        result.fetch('source_hashes_after_sha256') if mode=='cache-current'
        bound(files,after_path,result['source_hashes_after_sha256']) if result.key?('source_hashes_after_sha256')
        equal(files.json(after_path),expected_sources,'Parent audit after-source map differs')
        guarded(files,after_path,bindings)
      end
    end
    {'verification-driver.rb'=>'tool_sha256','process-monitor.rb'=>'monitor_sha256',
      'MERGED_SOURCES.json'=>'integration_registry_sha256','ENVIRONMENT.json'=>'environment_sha256'}.each do |p,key|
      bound(files,member.call(p),result.fetch(key))
    end
    # The archived registry binds the archived full snapshot. A normal proof
    # can precede unrelated source/scope edits; only its actual source/import
    # closure and pins must still match current inputs and compiled identities.
    files.json(member.call('MERGED_SOURCES.json')).fetch('sources').each do |path,row|
      equal(row.fetch('source'),path,'Parent registry source identity differs')
      equal(row.fetch('module').tr('.','/')+'.lean',path,'Parent registry module identity differs')
      equal(row.fetch('sha256'),run_sources.fetch(path),'Parent registry disagrees with original source snapshot')
    end
    environment=files.json(member.call('ENVIRONMENT.json'))
    equal(environment.fetch('pins').keys.sort,PINS.sort,'Incomplete parent pins')
    environment['pins'].each do |p,h|
      equal(run_sources.fetch(p),h,'Original parent pin hash differs')
      equal(expected_sources.fetch(p),h,'Parent pin hash differs')
    end
    revisions=result.fetch('dependency_revisions').to_h { |name,rev|['.lake/packages/'+name,rev] }
    equal(environment.fetch('revisions'),revisions,'Parent dependency revisions differ')
    inputs=files.json(member.call('INPUTS.json'))
    inputs.each { |k,v|equal(result.fetch(k),v,"Parent input/result disagreement: #{k}") unless k=='status' }
    process_path=member.call(result.fetch('process_receipt'))
    bound(files,process_path,result.fetch('process_receipt_sha256'))
    process=files.json(process_path)
    raise 'Parent child process did not pass' unless process['status']=='process-passed' && process['exit_code']==0 && process['signal'].nil? && process['guard_stop'].nil? && !process['failure']
    equal(process.fetch('proof_diagnostic_errors'),false,'Parent process reports proof errors')
    equal(process.fetch('log_recovery_verified'),true,'Parent gzip recovery not verified')
    raise 'Parent diagnostic examples present' unless process.fetch('diagnostic_examples',[]).empty?
    times=[result.fetch('started_utc'),process.fetch('started_utc'),process.fetch('finished_utc'),result.fetch('finished_utc')].map { |t|DateTime.iso8601(t) }
    raise 'Parent process chronology inconsistent' unless times.each_cons(2).all? { |a,b|a<=b }
    log_path=process_path.delete_suffix('.json')+'.log.gz'
    bound(files,log_path,process.fetch('log_compressed_sha256'))
    digest=Digest::SHA256.new;markers=[]
    Zlib::GzipReader.open(files.path(log_path)) do |io|
      io.each_line do |line|
        raise 'Error/PANIC/sorry in original process log' if line.match?(/\berror(?:\([^\n]*\))?:|\bPANIC\b|\bsorry\b/)
        digest.update(line)
        markers<<line.strip if line.start_with?('SHARED EXTRACTION COMPLETE:')
      end
    end
    equal(digest.hexdigest,process.fetch('log_plain_sha256'),'Original decompressed log hash differs')
    if process.key?('log_sha256')
      equal(process['log_sha256'],digest.hexdigest,'Pre-existing process alias differs')
    end
    if !%w[cache-hashes cache-current].include?(mode)
      equal(result.fetch('source_to_object_bindings_verified'),true,'Parent imported-object verification missing')
      object_path=member.call('IMPORTED_OBJECTS.json')
      bound(files,object_path,result.fetch('imported_objects_sha256'))
      imports=files.json(object_path)
      imports.each do |mod,entry|
        equal(entry.fetch('source'),mod.tr('.','/')+'.lean','Imported source/module differs')
        equal(entry.fetch('source_sha256'),run_sources.fetch(entry['source']),'Imported source differs from original snapshot')
        equal(entry.fetch('source_sha256'),expected_sources.fetch(entry['source']),'Imported source is stale')
        equal(entry.fetch('object'),'.lake/build/lib/lean/'+mod.tr('.','/')+'.olean','Imported object/module differs')
        hash!(entry.fetch('object_sha256'))
        raise 'Unknown imported-object basis' unless %w[fresh-canonical-proof-check validated-published-baseline-cache].include?(entry.fetch('basis'))
        if normal_mode
          current=current_objects.fetch(mod) { raise "Current imported-object binding missing: #{mod}" }
          equal(OBJECT_FIELDS.map { |f|entry.fetch(f) },OBJECT_FIELDS.map { |f|current.fetch(f) },"Current imported-object identity differs: #{mod}")
        end
      end
    end
    if mode=='cache-current'
      cache_binding=cache_current(files,result_path,result,process,expected_sources,bindings)
    elsif %w[build root].include?(mode)
      name=result.fetch('name');raise 'Noncanonical checked module' unless name.match?(/\AAtlas(?:\.[A-Za-z0-9_]+)*\z/)
      source=name.tr('.','/')+'.lean'
      equal(result.fetch('source'),source,'Parent source/name differs')
      equal(result.fetch('source_sha256'),run_sources.fetch(source),'Checked source differs from original snapshot')
      equal(result.fetch('source_sha256'),expected_sources.fetch(source),'Parent checked source is stale')
      object='.lake/build/lib/lean/'+name.tr('.','/')+'.olean'
      equal(result.fetch('compiled_object'),object,'Parent compiled object belongs to another source')
      hash!(result.fetch('compiled_sha256'))
      current=current_objects.fetch(name) { raise 'Current checked-object binding missing' }
      equal(current.values_at('source','source_sha256','object','object_sha256','basis'),
        [source,result['source_sha256'],object,result['compiled_sha256'],'fresh-canonical-proof-check'],
        'Current checked source/object identity differs')
      candidate=result.fetch('candidate');command=process.fetch('command')
      equal(process.fetch('cwd'),candidate,'Wrong normal-proof working directory')
      equal(process.fetch('environment').fetch('LEAN_NUM_THREADS'),'2','Wrong normal-proof thread setting')
      raise 'Wrong normal Lean options' unless (OPTIONS-command).empty? && (command.include?('-j1') || command.include?('-j2')) && !command.include?('--run')
      equal(command.last,candidate+'/'+source,'Normal child checked a different source')
      raise 'Normal root option differs' unless command.include?('--root='+candidate)
      oi=command.index('-o');ii=command.index('-i')
      equal(oi && command[oi+1],candidate+'/'+object,'Normal object output differs')
      equal(ii && command[ii+1],candidate+'/'+object.delete_suffix('.olean')+'.ilean','Normal interface output differs')
    elsif FULL_MODES.include?(mode)
      equal(result.fetch('full_dependency_audit'),true,'Parent result is not a full audit')
      manifest_path=member.call(mode=='audit-batch' ? 'BATCH_CHECKPOINT.json' : 'MANIFEST.json')
      manifest=files.json(manifest_path)
      equal(manifest.values_at('mode','definitions'),['full',true],'Parent manifest lacks full definitions')
      equal(result.fetch('allowed_axioms').sort,AXIOMS.sort,'Parent allowed axioms differ')
      equal(manifest.fetch('allowed_axioms').sort,AXIOMS.sort,'Parent manifest axioms differ')
      raise 'Parent axiom report is forbidden' unless (result.fetch('axioms')-AXIOMS).empty?
      registered=mode=='audit' ? result.fetch('registered_scope') : {}
      manifest_hash=case mode
      when 'audit' then registered.fetch('sha256')
      when 'audit-batch' then result.fetch('batch_manifest_sha256')
      when 'audit-public' then result.fetch('public_manifest_sha256')
      end
      bound(files,manifest_path,manifest_hash)
      if mode=='audit-public'
        path=member.call('PUBLIC_AUDIT_REGISTRY.json')
        bound(files,path,result.fetch('public_registry_sha256'))
        guarded(files,path,bindings)
      end
      if mode=='audit-batch'
        bound(files,member.call('BATCH_REGISTRY.json'),result.fetch('batch_registry_sha256'))
        bound(files,member.call('audit_batch_support.rb'),result.fetch('audit_batch_helper_sha256'))
        bound(files,member.call('BATCH_EVIDENCE.json'),result.fetch('batch_evidence_sha256'))
        evidence=files.json(member.call('BATCH_EVIDENCE.json'))
        equal(evidence.fetch('original_process'),{'path'=>result['process_receipt'],'sha256'=>result['process_receipt_sha256']},'Batch evidence names a different original process')
        equal(evidence.fetch('parent_result'),'RESULT.json','Batch evidence names a different outer result')
        equal(evidence.fetch('parent_result_required_status'),result['status'],'Batch/parent success status contract differs')
        equal(evidence.fetch('registered_batch_sha256'),result.fetch('batch_manifest_sha256'),'Batch manifest registration differs')
        equal(evidence.fetch('registry_sha256'),result.fetch('batch_registry_sha256'),'Batch evidence registry differs from original parent')
        equal(evidence.fetch('scopes').size,result.fetch('batch_scopes'),'Batch scope count differs from original parent')
        registry=files.json(member.call('BATCH_REGISTRY.json'))
        equal(registry.fetch('producer_bindings').fetch('batch_helper').fetch('sha256'),result['audit_batch_helper_sha256'],'Parent used a different registered batch helper')
        guarded(files,member.call('BATCH_EVIDENCE.json'),bindings)
      end
      equal(result.fetch('targets'),manifest.fetch('targets').size,'Parent target count differs')
      raise 'Missing completed extraction marker' unless markers.include?("SHARED EXTRACTION COMPLETE: #{result['targets']} targets")
      declarations=files.read(member.call('declarations.jsonl')).lines.map { |line|JSON.parse(line) }
      equal(declarations.map { |d|d.fetch('declaration') },manifest['targets'].map { |t|t.fetch('declaration') },'Parent declaration selection differs')
      declarations.zip(manifest['targets']).each { |d,t|equal(d.fetch('module'),t.fetch('module'),'Parent declaration module differs') }
      equal(result.fetch('axioms').sort,declarations.flat_map { |d|d.fetch('axioms') }.uniq.sort,'Parent axiom summary differs')
      equal(result.fetch('boundaries').map { |b|b.fetch('id') },manifest.fetch('boundaries',[]).map { |b|b.fetch('id') },'Parent policy outcome selection differs')
      raise 'Parent boundary did not pass' unless result['boundaries'].all? { |b|b['status']=='passed' && b.fetch('roots')>0 }
      graph_binding=graph_representation(files,result_path,result)
      [manifest_path,member.call('declarations.jsonl'),member.call('dependencies.jsonl.gz')].each { |p|guarded(files,p,bindings) }
      if registered['original_receipt']
        equal(result.fetch('historical_policy_sha256'),registered.fetch('original_manifest_sha256'),'Parent original policy hash differs')
        raise 'Original transported policy did not pass' unless result.fetch('historical_policy_boundaries_on_current_graph').all? { |b|b['status']=='passed' && b.fetch('roots')>0 }
        raise 'Missing historical policy transport account' if result.fetch('historical_policy_transport').empty?
      end
    end
    {result:result,process:process,process_path:process_path,log_path:log_path,plain_sha256:digest.hexdigest,
      source_hashes_path:sources_path,result_path:result_path,guarded_bindings:bindings,graph_representation:graph_binding,cache_binding:cache_binding}
  end
end
