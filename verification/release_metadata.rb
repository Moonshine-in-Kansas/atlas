# Local consistency and publication gates. No proof runs or network operations.
require 'json'
require 'digest'
require 'pathname'
require 'zlib'
require_relative 'existence/contracts' unless defined?(AtlasContracts::Index)
require_relative 'release_evidence'

module AtlasReleaseMetadata
  ROOT=File.expand_path('..',__dir__)
  MANIFESTS=%w[RELEASE_MANIFEST.json SHA256SUMS verification/release-candidate/PACKAGE_SHA256SUMS].freeze
  CHECKS=%w[build_audit nanoda interface_comparator].freeze
  class Gate
    attr_reader :files,:index,:sources,:roots,:contracts,:cache,:nanoda,:blockers,:successor,:additions
    def initialize(root=ROOT,reader:nil)
      @files=reader || AtlasContracts::Index.new(root)
      @index=files.json('verification/current.json')
      raise 'Expected Version 1.2 metadata' unless index['format']==2 && index['release_version']=='1.2'
      raise 'Wrong metadata paths' unless index.values_at('sources','roots','contracts')==
        %w[verification/release-candidate/SOURCE_HASHES.json verification/roots.json verification/existence/registry.json]
      raise 'Unknown or missing acceptance checks' unless index.fetch('checks').keys.sort==CHECKS.sort
      raise 'Successor evidence requires source update' if index.dig('supplemental_cache_audit','format')==2 && !index.key?('source_update')
      raise 'Unindexed public checkpoint file' if File.exist?(files.root+'/catalogue/checkpoints.json') && !index['completed_checkpoints']
    end
    def equal(actual,expected,message)
      raise message unless actual==expected
    end
    def inventory
      Dir.glob(files.root+'/**/*',File::FNM_DOTMATCH).reject { |p|File.directory?(p) && !File.symlink?(p) }
        .map { |p|p.delete_prefix(files.root+'/') }.reject { |p|p.start_with?('.git/','.lake/','verification/results/') }.sort
    end
    def validate_sources!
      paths=(Dir.glob(files.root+'/Atlas/**/*.lean').map { |p|p.delete_prefix(files.root+'/') }+
        %w[Atlas.lean lean-toolchain lakefile.toml lake-manifest.json]).sort
      @sources=paths.to_h { |p|[p,files.sha(p)] }
      equal(sources,files.json(index.fetch('sources')),'Sources or dependency pins changed; new verification required')
      @roots=files.json(index.fetch('roots'))
      refs={}
      collect=lambda do |x|
        case x
        when Hash
          if x['declaration'].is_a?(String) && x['source'].is_a?(String)
            p=x.fetch('source')
            files.path(p) unless p.start_with?('.lake/packages/mathlib/')
            r={'declaration'=>x['declaration'],'module'=>p.delete_prefix('.lake/packages/mathlib/').delete_suffix('.lean').tr('/','.'),'kind'=>'any'}
            raise 'Conflicting declaration sources' if refs.key?(r['declaration']) && refs[r['declaration']]!=r
            refs[r['declaration']]=r
          end
          x.each_value { |v|collect.call(v) }
        when Array then x.each { |v|collect.call(v) }
        end
      end
      %w[catalogue/catalogue.json catalogue/realizations.json catalogue/comparisons.json].each { |p|collect.call(files.json(p)) }
      collect.call(AtlasReleaseEvidence.checkpoints(files,index))
      equal(roots,refs.values.sort_by { |r|r['declaration'] },'Catalogue, realizations, comparisons and audit roots differ')
      raise 'Empty audit target selection' if roots.empty?
    end
    def validate_measurement!
      m=files.json('catalogue/measurement.json')
      equal(m['format'],2,'Old measurement schema')
      equal(files.sha(m.fetch('original_evidence')),m.fetch('original_evidence_sha256'),'Changed measurement evidence')
      equal(files.sha(m.fetch('counts')),m.fetch('counts_sha256'),'Changed dependency counts')
      entries=files.json('catalogue/catalogue.json').fetch('entries')
      equal(m.fetch('entries').keys.sort,entries.map { |e|e['id'] }.sort,'Incomplete measurement coverage')
      entries.each do |e|
        r=m['entries'].fetch(e['id']);p=e.fetch('proof_dependencies')
        equal(r.fetch('diagram'),p,'Wrong diagram binding')
        equal(files.sha(p),r.fetch('diagram_sha256'),'Changed measured diagram')
        data=JSON.parse(files.read(p)[/<script id="data" type="application\/json">(.*?)<\/script>/m,1])
        equal(data.fetch('roots'),r.fetch('roots'),'Changed measured roots')
        equal(data.fetch('source_hashes'),r.fetch('sources'),'Changed measurement source set')
        r.fetch('sources').each { |src,h|equal(files.sha(src),h,"Stale diagram source: #{src}") }
      end
    end
    def process!(r)
      raise 'Unsuccessful or memory-stopped process' unless r['status']=='process-passed' && r['exit_code']==0 && r['signal'].nil? && r['guard_stop'].nil?
    end
    def validate_cache!
      if index['source_update']
        @additions=AtlasReleaseEvidence::Successor.new(files,index,sources,roots,whole:false).validate!
      end
      if index.dig('supplemental_cache_audit','format')==2
        @successor=AtlasReleaseEvidence::Successor.new(files,index,sources,roots).validate!
        @cache=successor.record
        return
      end
      ptr=index.fetch('supplemental_cache_audit');dir=ptr.fetch('directory')
      bundle=files.validate_bundle(dir,ptr.fetch('bundle_sha256'))
      @cache=files.json(dir+'/RESULT.json')
      equal(cache.fetch('status'),'passed-source-bound-cache-audit','Wrong supplemental audit status')
      equal(cache.fetch('fresh_project_rebuild'),false,'Cache audit cannot be promoted to a fresh project rebuild')
      equal(cache.fetch('independent_replay'),false,'Cache audit cannot be promoted to independent replay')
      equal(files.json(dir+'/SOURCE_HASHES.json'),sources,'Cache audit does not bind current sources')
      equal(files.json(dir+'/roots.json'),roots,'Cache audit targets changed')
      equal(cache.fetch('roots'),roots.size,'Cache audit root count differs')
      raise 'Cache or sources changed during audit' unless cache['cache_artifacts_unchanged'] && cache['sources_unchanged']
      equal(cache.fetch('axioms').sort,AtlasContracts::AXIOMS.sort,'Unexpected audit axioms')
      pins=files.json('lake-manifest.json').fetch('packages').to_h { |p|[p.fetch('name'),p.fetch('rev')] }
      equal(cache.fetch('dependency_revisions'),pins,'Audit dependency revisions changed')
      equal(cache.fetch('steps').map { |r|r['name'] },%w[cache-hashes root-elaboration audit-root-elaboration full-dependency-extraction],'Incomplete cached audit')
      cache.fetch('steps').each do |s|
        equal(s.fetch('status'),'process-passed','Unsuccessful cached audit step')
        process!(files.json(dir+'/'+s.fetch('record')))
      end
      records=files.read(dir+'/declarations.jsonl').lines.map { |l|JSON.parse(l) }
      equal(records.map { |r|r.fetch('declaration') }.sort,roots.map { |r|r['declaration'] }.sort,'Incomplete compiled declarations')
      raise 'Unapproved declaration axioms' unless records.all? { |r|(r.fetch('axioms')-AtlasContracts::AXIOMS).empty? }
      bundle.fetch('uncompressed_hashes').each do |p,h|
        full=files.path(dir+'/'+p+'.gz')
        digest=Digest::SHA256.new
        Zlib::GzipReader.open(full) { |g|digest.update(g.read(1024*1024)) until g.eof? }
        equal(digest.hexdigest,h,"Changed compressed audit artifact #{p}")
      end
      if additions
        # The original four-step format is retained. New runs must use the exact
        # export cache and pass the same original process/log checks as scopes.
        equal(files.json(dir+'/CACHE_SOURCE_HASHES.json'),sources,'Successor cache does not bind exact exported bytes')
        equal(files.json(dir+'/SOURCE_HASHES_AFTER.json'),sources,'Successor sources changed during audit')
        AtlasReleaseEvidence.cache_artifacts!(files,dir,sources)
        %w[fresh_project_rebuild independent_replay].each { |key|equal(cache.fetch(key),false,'Supplemental evidence is not acceptance') }
        # Preserve the historical four-step format, but new extraction/root
        # successes must survive the original outer verifier's final guard.
        bound=AtlasReleaseEvidence::Successor.new(files,index,sources,roots)
        bound.instance_variable_set(:@bundle,bundle)
        bound.instance_variable_set(:@update_date,Date.iso8601(index['source_update'].fetch('authorized_on')))
        cache.fetch('steps').each do |step|
          if step.fetch('name')=='full-dependency-extraction'
            targets,_declarations,_graph,_process,_parent=bound.extraction!(step)
            equal(targets,roots,'Whole public-root extraction scope differs')
            equal(files.sha(dir+'/'+step.fetch('declarations')),files.sha(dir+'/declarations.jsonl'),'Whole-root declaration alias differs')
            equal(files.sha(dir+'/'+step.fetch('log')),files.sha(dir+'/full-dependency-extraction.log.gz'),'Whole-root statement log alias differs')
          else
            bound.cache_step!(step)
          end
        end
        cache.fetch('steps').each do |step|
          r=files.json(dir+'/'+step.fetch('record'))
          raise 'Historical process relabelled as successor' if Date.iso8601(r.fetch('started_utc')[0,10])<Date.iso8601(index['source_update'].fetch('authorized_on'))
          name=step.fetch('name')+'.log'
          p=step.fetch('log')
          raise 'Missing successor process log' unless bundle.fetch('files').key?(p)
          digest=Digest::SHA256.new
          io=p.end_with?('.gz') ? Zlib::GzipReader.open(files.path(dir+'/'+p)) : File.open(files.path(dir+'/'+p))
          begin
            io.each_line do |line|
              raise 'Error/PANIC/sorry in successor log' if line.match?(/\berror:|\bPANIC\b|\bsorry\b/)
              digest.update(line)
            end
          ensure
            io.close
          end
          equal(digest.hexdigest,r.fetch('log_sha256'),'Original successor log binding differs')
        end
      end
    end
    def validate_history!
      pointer=index.fetch('dated_nanoda');dir=pointer.fetch('directory')
      files.validate_bundle(dir,pointer.fetch('bundle_sha256'))
      @nanoda=files.json(dir+'/KERNEL_RESULT.json')
      equal(nanoda['status'],'passed-kernel-check-with-pretty-printer-warning','Changed historical Nanoda outcome')
      raise 'Historical Nanoda errors' unless nanoda['checker_exit_code']==0 && nanoda['typechecker_errors']==0
      original=files.json(index.fetch('prior_accepted_release'))
      equal(files.sha(index['prior_accepted_release']),index.fetch('prior_accepted_release_sha256'),'Changed v1.0 baseline')
      raise 'Lost prior evidence pointer' unless original['snapshot'] && original['evidence_files']
      @contracts=files.validate!
      equal(index.fetch('deferred_contracts').sort,contracts.fetch(:open),'Deferred targets must remain explicitly open')
    end
    # Future accepted runs use a separately reviewed receipt, never a relabelled
    # historical RESULT. Hashes establish applicability, not execution attestation.
    def validate_acceptance!
      @blockers=[]
      CHECKS.each do |kind|
        ptr=index['checks'][kind]
        unless ptr
          blockers<<"Current-export #{kind.tr('_',' ')} acceptance is pending"
          next
        end
        dir=ptr.fetch('directory');files.validate_bundle(dir,ptr.fetch('bundle_sha256'))
        result=files.json(dir+'/ACCEPTANCE.json')
        equal(result.values_at('format','check','status'),[1,kind,'passed'],'Unsupported or unsuccessful acceptance receipt')
        equal(files.json(dir+'/SOURCE_HASHES.json'),sources,'Accepted run has stale source/pin hashes')
        equal(files.json(dir+'/roots.json'),roots,'Accepted run has stale roots')
        equal(result.fetch('allowed_axioms').sort,AtlasContracts::AXIOMS.sort,'Unapproved acceptance axioms')
        equal(result.fetch('sources_unchanged'),true,'Sources changed during accepted run')
        result.fetch('processes').each { |p|process!(files.json(dir+'/'+p)) }
        raise 'Missing accepted process receipts' if result['processes'].empty?
        actual=files.json(dir+'/RESULT.json')
        equal(actual.fetch('status'),'passed','Original run did not pass')
        equal(actual.fetch('roots'),roots.size,'Original run has wrong target count')
        if kind=='build_audit'
          equal(result.fetch('fresh_project_rebuild'),true,'Full project proof recheck required; cache audit is supplemental')
          equal(result.fetch('full_dependency_audit'),true,'Full dependency audit required')
          raise 'Missing build/audit evidence' unless actual.fetch('dependency_nodes')>0 && files.path(dir+'/declarations.jsonl') && files.path(dir+'/dependencies.jsonl.gz')
        else
          equal(result.fetch('independent_replay'),true,'Independent replay required')
          if kind=='nanoda'
            raise 'Missing successful Nanoda export/replay' unless actual.fetch('checked_declarations')>0 && actual.fetch('export_sha256').match?(/\A[0-9a-f]{64}\z/)
          else
            equal(result.fetch('definition_holes'),0,'Interface Comparator definition holes')
            targets=files.json(dir+'/comparator-targets.json')
            equal(targets.map { |r|r.fetch('original') }.sort,roots.map { |r|r['declaration'] }.sort,'Incomplete interface comparison')
          end
        end
      end
      contracts.fetch(:open).each { |n|blockers<<"Comparator target remains open: #{n}" }
      blockers
    end
    # Editable publication is separate from acceptance of a frozen release.
    # This owner-approved scope binds the mathematical export and its evidence;
    # it never changes a checker outcome or fills an acceptance slot.
    def validate_working_publication!
      authorization=index.fetch('working_publication') { raise 'Missing working-publication authorization' }
      equal(authorization.values_at('format','version','branch','mutable'),[1,'1.2','main',true],
        'Wrong working-publication scope')
      equal(authorization.fetch('authorized_on'),'2026-10-27','Wrong working-publication decision date')
      raise 'Missing owner decision' unless authorization.fetch('owner_decision').include?('main working (modifable) version')
      paths=[index.fetch('sources'),index.fetch('roots'),index.fetch('contracts'),index.fetch('prior_accepted_release'),
        index.fetch('supplemental_cache_audit').fetch('directory')+'/BUNDLE.json',
        index.fetch('dated_nanoda').fetch('directory')+'/BUNDLE.json']
      if index['source_update']
        paths.concat(AtlasReleaseEvidence::REGISTRIES)
        paths.concat(index.fetch('source_update').values_at('previous_index','previous_manifest'))
        paths<<index.fetch('source_update').fetch('proof_evidence').fetch('directory')+'/BUNDLE.json'
        paths<<index['completed_checkpoints'] if index['completed_checkpoints']
        equal(authorization.fetch('source_update'),index.fetch('source_update'),'Working-publication update instruction differs')
      end
      equal(authorization.fetch('bindings'),paths.to_h { |p|[p,files.sha(p)] },
        'Working-publication source, target or evidence binding changed')
      equal(authorization.fetch('allowed_pending_checks').sort,CHECKS.sort,'Wrong allowed pending checks')
      equal(authorization.fetch('allowed_open_contracts').sort,AtlasContracts::DEFERRED.sort,'Wrong allowed open contracts')
      raise 'Unapproved pending checks' unless (index['checks'].select { |_,v|v.nil? }.keys-authorization['allowed_pending_checks']).empty?
      raise 'Unapproved open contracts' unless (contracts.fetch(:open)-authorization['allowed_open_contracts']).empty?
    end
    def validate_layout!
      raise 'Obsolete docs directory' if Dir.exist?(files.root+'/docs')
      inventory.each do |p|
        files.path(p)
        raise "Internal construction note in release: #{p}" if p.match?(%r{(?:\A|/)(?:AGENTS\.md|JOB_[^/]*|[^/]*(?:_PROJECT|_PROGRESS|_RESUME|_HANDOFF|_PREREQUISITES)\.md|claude(?:/|\z))})
      end
      equal(files.read('atlas_research_note.pdf')[0,5],'%PDF-','Missing research PDF')
      raise 'Missing PDF link' unless files.read('README.md').include?('](atlas_research_note.pdf)')
      raise 'Approved license changed' unless files.read('LICENSE').include?('ATLAS Research and Attribution License')
      pages=%w[README.md CATALOGUE.md COMPARISON.md THEOREM_STATEMENTS.md AUDIT.md LICENSING.md
        catalogue/README.md catalogue/REALIZATIONS.md catalogue/COMPARISONS.md catalogue/ISOMORPHISMS.md
        verification/README.md verification/MAINTENANCE.md verification/INDEPENDENT_CHECKERS.md
        verification/existence/README.md verification/existence/RESULTS.md verification/comparisons/README.md]
      pages<<'catalogue/CHECKPOINTS.md' if index['completed_checkpoints']
      pages.each do |p|
        files.read(p).scan(/\]\(([^\s)]+)(?:\s+"[^"]*")?\)/).flatten.each do |url|
          next if url.match?(%r{\A(?:https?://|mailto:|#)})
          target=File.expand_path(url.split('#',2).first,File.dirname(files.root+'/'+p))
          raise "Escaping link #{p}: #{url}" unless target.start_with?(files.root+'/')
          raise "Broken link #{p}: #{url}" unless File.exist?(target)
        end
      end
    end
    def audit_text
      dir=index.fetch('supplemental_cache_audit').fetch('directory')
      if successor
        facts=successor.summary
        peak=facts.fetch(:peak_owned_rss_and_swap)
        audit_row="[Exact-export successor audit](#{dir}/CACHE_AUDIT.json) | #{facts[:roots]} roots; #{facts[:scopes]} full scopes; #{facts[:dependency_node_occurrences]} dependency-node occurrences (scopes may overlap); only permitted logical axioms"
        provenance="The successor audit uses the exact exported source bytes, with normal source proof checks for every new or changed Lean file. Original process receipts and complete per-scope dependency graphs are retained. The [published baseline](#{index['source_update']['previous_index']}) and its dated evidence are preserved; old successes are not relabelled."
      elsif additions
        peak=cache.fetch('steps').map { |s|files.json(dir+'/'+s['record']).fetch('peak_owned_rss_and_swap',0) }.max
        audit_row="[Exact-export compiled audit](#{dir}/RESULT.json) | #{cache['roots']} roots; #{cache['dependency_nodes']} complete type/proof dependency nodes; only the three permitted logical axioms"
        provenance="The successor audit uses the exact exported source bytes. The [additional proof evidence](#{additions.directory}/ADDITIONS.json) records normal source proof checks and full checkpoint policies. The [published baseline](#{index['source_update']['previous_index']}) and its dated evidence remain unchanged."
      else
        peak=cache.fetch('steps').map { |s|files.json(dir+'/'+s['record']).fetch('peak_owned_rss_and_swap',0) }.max
        audit_row="[26 October compiled audit](#{dir}/RESULT.json) | #{cache['roots']} roots; #{cache['dependency_nodes']} complete type/proof dependency nodes; only the three permitted logical axioms"
        provenance="The historical source copies differ only by recorded licence comments and package version metadata; the filtered root import has its own fresh elaboration."
      end
      <<~MD
        # Verification of Version 1.2

        <!-- Generated by verification/release_metadata.rb; do not edit by hand. -->
        **Version 1.2 is the editable version on `main`; frozen-release acceptance remains pending.** The
        [current index](verification/current.json) keeps successful dated checks,
        the supplemental audit and outstanding verification requirements separate.

        | Check | Recorded result | Scope |
        |---|---|---|
        | #{audit_row} | Fresh elaboration of both import roots using a validated, unchanged cache; not a fresh whole-project rebuild or independent replay |
        | [24 October Nanoda](#{index['dated_nanoda']['directory']}/README.md) | #{nanoda['checked_declarations']} declarations, no typechecker errors; pretty-printer warning retained | Broader dated development snapshot; explicit exclusions and original wrapper receipt preserved |
        | [25 October Comparator](verification/existence/RESULTS.md) | #{contracts[:passed]} of #{contracts[:total]} targets passed | 39 model-existence contracts, four strengthened contracts, two aggregate comparison contracts; three memory-stopped targets remain open |

        The supplemental audit binds every current source and dependency pin, all
        #{roots.size} catalogue/realization/comparison/checkpoint roots, and the cached artifacts.
        Its peak owned RSS plus swap was #{format('%.2f',peak.to_f/1024**3)} GiB.
        #{provenance}
        The allowed axioms are `propext`, `Classical.choice` and `Quot.sound`.

        The three deferred targets are Albert-model F₄, `AtlasComparison.main` and
        `AtlasComparison.nonisomorphic`. The Chevalley F₄ pass does not establish the
        Albert-model contract. None of the three incomplete results is counted as a pass.
        Existence contracts certify their specified witnesses and parameter ranges;
        they do not imply external recognition or replace the full interface audit.

        ## Remaining requirements before freezing Version 1.2

        #{blockers.map { |b|"- #{b}." }.join("\n")}

        The owner authorized editable publication on 27 October 2026, with these
        requirements still open. The three deferred targets are not retried or
        counted as passed. Version 1.2 can receive later updates on `main`;
        [Version 1.0](https://github.com/Moonshine-in-Kansas/atlas/releases/tag/v1.0)
        remains an immutable release. No frozen Version 1.2 release is claimed.
        This export includes no construction-job documents or internal progress notes.

        ## Reproduction and maintenance

        See [Lean verification](verification/README.md),
        [independent checkers](verification/INDEPENDENT_CHECKERS.md), and
        [maintenance](verification/MAINTENANCE.md). For metadata only:

        ```sh
        ruby verification/release_metadata.rb refresh
        ruby verification/release_metadata.rb check-preparation
        ruby verification/release_metadata.rb check-working
        ruby verification/release_metadata.rb check
        ```

        The first two commands maintain and validate the export. `check-working`
        additionally requires the source- and evidence-bound owner authorization
        for editable publication. The pre-push hook and Pages workflow use it for
        `main`. The last command is the strict frozen-release gate and refuses
        pending acceptance; tags and other branches require it. The retained
        `v1.2-review` branch uses preparation validation. Every push requires a
        clean checkout and a matching commit; a mixed push uses the strictest gate.
        All commands above are local and
        run no proofs. Hashes bind applicability; they are not execution attestations.
      MD
    end
    def write_or_check(p,text,mode)
      full=File.join(files.root,p)
      raise "Symlinked generated output #{p}" if File.symlink?(full)
      if mode=='refresh'
        File.write(full,text)
      else
        equal(files.read(p),text.b,"Stale #{p}; run metadata refresh")
      end
    end
    def manifests!(mode)
      hashes=(inventory-MANIFESTS).to_h { |p|[p,files.sha(p)] }
      manifest=JSON.pretty_generate({'format'=>2,'version'=>'1.2','toolchain'=>files.read('lean-toolchain').strip,
        'dependencies'=>files.json('lake-manifest.json'),'verification'=>'verification/current.json','files'=>hashes})+"\n"
      sums=hashes.merge('RELEASE_MANIFEST.json'=>Digest::SHA256.hexdigest(manifest)).sort.map { |p,h|"#{h}  #{p}\n" }.join
      package=hashes.merge('RELEASE_MANIFEST.json'=>Digest::SHA256.hexdigest(manifest),'SHA256SUMS'=>Digest::SHA256.hexdigest(sums))
        .sort.map { |p,h|"#{h}  #{p}\n" }.join
      write_or_check('RELEASE_MANIFEST.json',manifest,mode)
      write_or_check('SHA256SUMS',sums,mode)
      write_or_check('verification/release-candidate/PACKAGE_SHA256SUMS',package,mode)
    end
    def run(mode)
      raise 'Unknown mode' unless %w[refresh check-preparation check-working check].include?(mode)
      validate_sources!;validate_measurement!;validate_cache!;validate_history!;validate_acceptance!
      validate_working_publication!
      generated_mode=mode=='refresh' ? 'refresh' : 'check'
      %w[verification/existence/sync.rb catalogue/manage.rb].each do |script|
        raise "Generated metadata failed: #{script}" unless system('ruby',files.root+'/'+script,generated_mode)
      end
      write_or_check('AUDIT.md',audit_text,mode)
      validate_layout!;manifests!(mode)
      raise "Frozen-release acceptance remains pending:\n  "+blockers.join("\n  ") if mode=='check' && !blockers.empty?
      puts "PASS: Version 1.2 metadata, #{roots.size} roots, #{contracts[:total]} contracts and complete file manifests (#{mode}). Frozen-release acceptance #{blockers.empty? ? 'complete' : 'pending'}; no proof replay."
    end
  end
end
if $PROGRAM_NAME==__FILE__
  begin
    AtlasReleaseMetadata::Gate.new.run(ARGV.fetch(0,'check'))
  rescue StandardError=>e
    warn "Release check refused: #{e.message}"
    exit 1
  end
end
