# Lossless metadata adapter for completed verify.rb runs. No driver is loaded.
# Original receipts/logs stay exact. A verified gzip may represent the original
# dependency plaintext publicly; the private original is never removed/edited.
require 'json'
require 'digest'
require 'fileutils'
require 'pathname'
require_relative 'successor/verification/parent_receipts'

module AtlasVerifyReceiptAdapter
  PUBLIC_FILE_LIMIT=100*1024*1024
  class Reader
    attr_reader :root
    def initialize(root) = @root=File.realpath(root)
    def path(relative)
      raise 'Unsafe original artifact path' unless relative.is_a?(String) && !relative.empty? && !relative.start_with?('/') && relative.split('/').none? { |s|s.empty? || %w[. ..].include?(s) }
      parts=relative.split('/')
      raise 'Symlinked original artifact' if parts.each_index.any? { |i|File.symlink?(File.join(root,*parts[0..i])) }
      full=File.join(root,relative)
      raise 'Missing or escaping original artifact' unless File.file?(full) && File.realpath(full).start_with?(root+'/')
      full
    end
    def read(path) = File.binread(self.path(path))
    def json(path) = JSON.parse(read(path))
    def sha(path) = Digest::SHA256.file(self.path(path)).hexdigest
    def inventory
      Dir.glob(root+'/**/*',File::FNM_DOTMATCH).reject { |p|File.directory?(p) && !File.symlink?(p) }
        .map { |p|p.delete_prefix(root+'/') }.sort.to_h { |p|[p,sha(p)] }
    end
  end
  def self.write(path,data) = File.write(path,JSON.pretty_generate(data)+"\n")
  def self.check_public_sizes(files,members)
    members.each do |path|
      raise "Public artifact exceeds 100 MiB: #{path}" if File.size(files.path(path))>PUBLIC_FILE_LIMIT
    end
  end
  # Read-only planning API for the parent collector. `checked` must come from
  # AtlasParentReceipts.validate; inventory is the complete original inventory,
  # not a selected export list. No result, status or graph content is rewritten.
  def self.export_plan(files,checked,inventory:,prefix:'original')
    AtlasParentReceipts.within('.',prefix)
    retained=inventory.dup;compression={};plain_hashes={}
    if AtlasParentReceipts::FULL_MODES.include?(checked.fetch(:result).fetch('mode'))
      # Verify here as well so a collector cannot assert decoded equality merely
      # by constructing a `checked` hash. This is byte validation, not an audit.
      graph=AtlasParentReceipts.graph_representation(files,'RESULT.json',checked[:result])
      raise 'Graph representation changed during export planning' unless graph==checked.fetch(:graph_representation)
      plain=graph.fetch(:plain_path);gzip=graph.fetch(:compressed_path)
      raise 'Graph representation path differs from original stage' unless plain=='dependencies.jsonl' && gzip=='dependencies.jsonl.gz'
      raise 'Original inventory disagrees with plaintext presence' unless inventory.key?(plain)==graph.fetch(:plaintext_present)
      raise 'Original inventory gzip differs' unless inventory.fetch(gzip)==graph.fetch(:compressed_sha256)
      if inventory.key?(plain)
        raise 'Original inventory plaintext differs' unless inventory[plain]==graph.fetch(:plain_sha256)
        retained.delete(plain)
      end
      exported=AtlasParentReceipts.within(prefix,gzip)
      compression[plain]={'encoding'=>'gzip','exported_path'=>exported,
        'exported_sha256'=>graph[:compressed_sha256],'exported_bytes'=>graph[:compressed_bytes],
        'original_plain_sha256'=>graph[:plain_sha256],'uncompressed_bytes'=>graph[:plain_bytes],
        'original_inventory_contains_plaintext'=>inventory.key?(plain),'plaintext_copy_omitted'=>true,
        'decoded_sha256_verified'=>true,'original_result'=>AtlasParentReceipts.within(prefix,'RESULT.json'),
        'original_result_sha256'=>files.sha('RESULT.json'),'original_hash_field'=>'dependency_log_sha256',
        'private_originals_modified'=>false}
      plain_hashes[AtlasParentReceipts.within(prefix,plain)]=graph[:plain_sha256]
    end
    check_public_sizes(files,retained.keys)
    {'original_inventory'=>inventory.dup,'retained_inventory'=>retained,
      'compression_map'=>compression,'uncompressed_hashes'=>plain_hashes,'public_file_limit_bytes'=>PUBLIC_FILE_LIMIT}
  end
  def self.adapt(input,output,expected_sources,current_objects:nil)
    files=Reader.new(input);output=File.expand_path(output)
    raise 'Refusing existing adapter output' if File.exist?(output)
    raise 'Adapter output must be outside originals' if output==files.root || output.start_with?(files.root+'/')
    raise 'Output parent must already exist' unless File.directory?(File.dirname(output))
    original_inventory=files.inventory
    checked=AtlasParentReceipts.validate(files,'RESULT.json',expected_sources,current_objects:current_objects)
    plan=export_plan(files,checked,inventory:original_inventory)
    result=checked.fetch(:result);process=checked.fetch(:process)
    original_result={'path'=>'original/RESULT.json','sha256'=>files.sha('RESULT.json'),'status'=>result.fetch('status'),'mode'=>result.fetch('mode')}
    original_process={'path'=>'original/'+checked.fetch(:process_path),'sha256'=>files.sha(checked[:process_path])}
    derived_process=process.merge('log_sha256'=>checked.fetch(:plain_sha256),
      'adaptation'=>{'schema_version'=>1,'original_receipt'=>original_process,
        'alias'=>{'log_sha256'=>'log_plain_sha256'},'decompressed_log_verified'=>true,
        'original_compressed_sha256'=>process.fetch('log_compressed_sha256')})
    # All original fields remain present except the two explicitly translated
    # audit fields. Their exact previous values and complete bytes are retained.
    derived_result=result.merge('adaptation'=>{'schema_version'=>1,'producer'=>'verify.rb/2026-10-30',
      'original_result'=>original_result,'original_process'=>original_process,'field_changes'=>{}},
      'fresh_project_rebuild'=>result.fetch('fresh_whole_project_rebuild'))
    if AtlasParentReceipts::FULL_MODES.include?(result['mode'])
      manifest=files.json(result['mode']=='audit-batch' ? 'BATCH_CHECKPOINT.json' : 'MANIFEST.json')
      derived_result.merge!('status'=>'passed','mode'=>'full','checkpoint'=>manifest.fetch('id'))
      derived_result['adaptation']['field_changes']={'status'=>{'from'=>result['status'],'to'=>'passed'},'mode'=>{'from'=>result['mode'],'to'=>'full'}}
    end
    Dir.mkdir(output);Dir.mkdir(output+'/original')
    plan.fetch('retained_inventory').each do |path,hash|
      destination=output+'/original/'+path
      FileUtils.mkdir_p(File.dirname(destination))
      FileUtils.copy_file(files.path(path),destination)
      raise 'Original copy changed during adaptation' unless Digest::SHA256.file(destination).hexdigest==hash
    end
    raise 'Producer artifacts changed during adaptation' unless files.inventory==original_inventory
    write(output+'/PROCESS.json',derived_process)
    write(output+'/RESULT.json',derived_result)
    if %w[audit audit-public].include?(result['mode'])
      FileUtils.copy_file(files.path('MANIFEST.json'),output+'/CHECKPOINT.json')
      write(output+'/roots.json',files.json('MANIFEST.json').fetch('targets'))
    end
    binding={'schema_version'=>1,'status'=>'derived-from-original-success','original_result'=>original_result,
      'original_inventory'=>original_inventory,'process'=>'PROCESS.json','result'=>'RESULT.json',
      'compression_map'=>plan.fetch('compression_map'),'public_file_limit_bytes'=>PUBLIC_FILE_LIMIT,
      'scope'=>'Metadata adaptation only; no new proof, build, audit, independent replay or source check was performed.'}
    parent_fields={'parent_result'=>'original/RESULT.json','parent_result_sha256'=>original_result['sha256'],
      'record'=>'PROCESS.json','log'=>'original/'+checked.fetch(:log_path)}
    uncompressed={'original/'+checked[:log_path].delete_suffix('.gz')=>checked[:plain_sha256]}
    uncompressed.merge!(plan.fetch('uncompressed_hashes'))
    if %w[build root].include?(result['mode'])
      binding['normal_validation_scope']={'kind'=>'checked-source-transitive-imports-and-pins',
        'checked_source'=>result.fetch('source'),'imported_modules'=>files.json('IMPORTED_OBJECTS.json').keys.sort,
        'pins'=>AtlasParentReceipts::PINS,'original_full_source_snapshot'=>'original/SOURCE_HASHES.json',
        'current_object_bindings_required'=>true,'unrelated_source_changes_do_not_invalidate_this_proof'=>true}
      binding['normal_proof_row']={'id'=>result.fetch('name'),'sources'=>[result.fetch('source')],
        'fresh_source_check'=>true}.merge(parent_fields)
    elsif %w[audit audit-public].include?(result['mode'])
      binding['scope_artifacts']={'checkpoint'=>'CHECKPOINT.json','roots'=>'roots.json','result'=>'RESULT.json',
        'declarations'=>'original/declarations.jsonl','dependencies'=>'original/dependencies.jsonl.gz'}.merge(parent_fields)
    elsif result['mode']=='audit-batch'
      evidence=files.json('BATCH_EVIDENCE.json')
      prefix=->(row,keys) { row.to_h { |k,v|[k,keys.include?(k) ? 'original/'+v : v] } }
      binding['batch_artifacts']=prefix.call(evidence.fetch('batch'),%w[roots checkpoint result declarations dependencies source_hashes source_hashes_after]).merge(parent_fields)
      binding['scopes']=evidence.fetch('scopes').map { |row|prefix.call(row,%w[roots checkpoint result policy_results dependency_slice]) }
      policies=files.json(evidence.fetch('policy_inventory'))
      entries=policies.fetch('entries').map do |row|
        p=prefix.call(row,%w[manifest origin_map])
        p['module_transport']=row['module_transport'].merge('path'=>'original/'+row['module_transport'].fetch('path')) if row['module_transport']
        p
      end
      write(output+'/POLICIES.json',policies.merge('entries'=>entries,
        'adaptation'=>{'original_path'=>'original/'+evidence['policy_inventory'],'original_sha256'=>files.sha(evidence['policy_inventory']),
          'change'=>'Only bundle-relative manifest and origin-map pointer prefixes; original policy and origin-map bytes unchanged.'}))
      binding['policy_inventory']='POLICIES.json'
      binding['registry_sha256']=evidence.fetch('registry_sha256')
      evidence.fetch('uncompressed_hashes').each do |path,hash|
        digest=AtlasParentReceipts.gzip_facts(files,path+'.gz').fetch(:sha256)
        raise 'Original batch compressed artifact differs' unless digest==hash
        uncompressed['original/'+path]=hash
      end
    elsif %w[cache-hashes cache-current].include?(result['mode'])
      binding['cache_step']=parent_fields.merge('name'=>'cache-hashes','original_mode'=>result['mode'])
      if result['mode']=='cache-current'
        binding['cache_step']['operation']='current-cache-integrity'
        binding['cache_binding']='original/'+result.fetch('cache_binding')
        binding['cache_artifacts']=AtlasParentReceipts::CACHE_PAYLOADS.to_h { |p|[p,'original/cache/'+p] }
      end
    end
    write(output+'/ADAPTATION.json',binding)
    artifacts=Reader.new(output).inventory
    write(output+'/BUNDLE.json',{'format'=>1,'files'=>artifacts,'uncompressed_hashes'=>uncompressed})
    exported=Reader.new(output)
    check_public_sizes(exported,exported.inventory.keys)
    binding
  end
end
if $PROGRAM_NAME==__FILE__
  begin
    raise 'Usage: ruby verify_receipt_adapter.rb ORIGINAL_RUN NEW_OUTPUT CURRENT_SOURCE_HASHES.json [CURRENT_OBJECT_BINDINGS.json (required for build/root)]' unless [3,4].include?(ARGV.size)
    expected=JSON.parse(File.read(ARGV[2]))
    objects=ARGV[3] && JSON.parse(File.read(ARGV[3]))
    receipt=AtlasVerifyReceiptAdapter.adapt(ARGV[0],ARGV[1],expected,current_objects:objects)
    puts JSON.generate(receipt.slice('status','scope'))
  rescue StandardError=>e
    warn "Parent receipt adaptation refused: #{e.message}"
    exit 1
  end
end
