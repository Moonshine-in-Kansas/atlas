# Reviewed per-target specifications and immutable dated outcomes.
# No proof runs, deferred-target retries or publication acceptance occur here.
require 'json'
require 'digest'
require 'zlib'
require 'stringio'
module AtlasContracts
  ROOT=File.expand_path('../..',__dir__)
  AXIOMS=%w[propext Classical.choice Quot.sound].freeze
  DEFERRED=%w[AtlasExistence.F4 AtlasComparison.main AtlasComparison.nonisomorphic].sort.freeze
  class Index
    attr_reader :root,:registry
    def initialize(root=ROOT,registry:nil)
      @root=File.realpath(root)
      @registry=registry || json('verification/existence/registry.json')
    end
    def path(p)
      raise "Unsafe evidence path #{p.inspect}" unless p.is_a?(String) && !p.empty? && !p.start_with?('/') &&
        p.split('/').none? { |x|x=='.' || x=='..' || x.empty? } && !p.include?("\0")
      full=File.join(root,p)
      raise "Missing evidence #{p}" unless File.file?(full)
      raise "Evidence escapes release #{p}" unless File.realpath(full).start_with?(root+'/')
      raise "Symlinked evidence #{p}" if p.split('/').each_index.any? { |i|File.symlink?(File.join(root,*p.split('/')[0..i])) }
      full
    end
    def read(p)=File.binread(path(p))
    def sha(p)=Digest::SHA256.hexdigest(read(p))
    def json(p)=JSON.parse(read(p))
    def entries = registry.fetch('entries')
    def render(row)
      names=[row.fetch('reference_file'),row.fetch('solution_file'),row.fetch('configuration')]
      raise 'Unexpected contract filename' unless names.all? { |n|File.basename(n)==n }
      names.to_h { |n|[n,read(row.fetch('evidence')+'/'+n)] }
    end
    def validate_bundle(directory,expected_sha=nil)
      p=directory+'/BUNDLE.json'
      raise 'Reviewed evidence bundle changed' if expected_sha && sha(p)!=expected_sha
      bundle=json(p)
      inventory=Dir.glob(root+'/'+directory+'/**/*',File::FNM_DOTMATCH).select { |f|File.file?(f) || File.symlink?(f) }
        .map { |f|f.delete_prefix(root+'/'+directory+'/') }.reject { |f|f=='BUNDLE.json' }.sort
      raise 'Incomplete original artifact inventory' unless bundle.fetch('files').keys.sort==inventory
      bundle.fetch('files').each do |name,h|
        raise "Changed original artifact #{directory}/#{name}" unless sha(directory+'/'+name)==h
      end
      bundle
    end
    def validate!
      raise 'Expected Version 1.2 contract registry' unless registry['format']==2 && registry['version']=='1.2'
      directory=registry.fetch('bundle')
      bundle=validate_bundle(directory,registry.fetch('bundle_sha256'))
      original=json(directory+'/RESULT.json')
      expected=original.fetch('checks').flat_map { |r|r.fetch('targets') }.sort
      actual=entries.map { |r|r.fetch('declaration') }.sort
      raise 'Reviewed target selection changed' unless actual==expected && actual.uniq.size==45
      raise 'Wrong specification scopes' unless entries.group_by { |r|r.fetch('scope') }.transform_values(&:size)==
        {'comparison'=>2,'discriminator'=>4,'existence'=>39}
      catalogue=json('catalogue/catalogue.json').fetch('entries').map { |e|e.fetch('id') }.sort
      primary=entries.select { |r|r['primary_catalogue_contract'] }
      raise 'Incomplete or duplicate primary model coverage' unless primary.map { |r|r.fetch('catalogue_id') }.sort==catalogue
      raise 'Primary contracts must be existence targets' unless primary.all? { |r|r['scope']=='existence' }
      entries.each do |r|
        if r['scope']=='existence'
          raise 'Unregistered model contract' unless catalogue.include?(r['catalogue_id'])
          suffix=r.fetch('declaration').split('.').last
          chev=r['declaration'].start_with?('AtlasExistenceChevalley.')
          map=chev ? {'A'=>'PSL','B'=>'B','C'=>'C','D'=>'D','E6'=>'E6','E7'=>'E7','E8'=>'E8','F4'=>'F4','G2'=>'G2'} :
            {'cyclic'=>'Cyclic','alternating'=>'Alternating','typeA'=>'PSL','typeB'=>'B','typeC'=>'C','typeD'=>'D',
             'type2A'=>'PSU','type2D'=>'2D','G2'=>'G2','F4'=>'F4','SuzukiFamily'=>'Suzuki','Triality'=>'3D4','ReeG2'=>'ReeG2'}
          model=suffix=='Tits' ? 'exceptional.Tits' : map.key?(suffix) ? 'family.'+map.fetch(suffix) : 'sporadic.'+suffix
          primary=!chev || %w[E6 E7 E8].include?(suffix)
          raise 'Wrong concrete model binding' unless r['catalogue_id']==model && r['primary_catalogue_contract']==primary &&
            r['realization']==(chev ? 'chevalley' : 'catalogue-default')
          raise 'Wrong primary E-series binding' if %w[family.E6 family.E7 family.E8].include?(r['catalogue_id']) &&
            (!r['primary_catalogue_contract'] || r['realization']!='chevalley')
        else
          raise 'Nonexistence target counted as a model' if r['catalogue_id'] || r['primary_catalogue_contract']
        end
      end
      seen={}
      results=entries.map do |row|
        evidence=row.fetch('evidence')
        raise 'Evidence outside reviewed bundle' unless evidence.start_with?(directory+'/') && evidence.delete_prefix(directory+'/').split('/').size==1
        record=json(evidence+'/RESULT.json')
        anchor=original['checks'].find { |r|r['id']==record['id'] }
        raise 'Per-target receipt differs from original queue' unless anchor==record
        raise 'Wrong receipt target' unless record.fetch('targets').include?(row['declaration'])
        rendered=render(row);reviewed=row.fetch('reviewed_inputs')
        raise 'Contract inventory mismatch' unless rendered.keys.sort==reviewed.keys.sort
        rendered.each do |p,bytes|
          h=Digest::SHA256.hexdigest(bytes)
          raise "Changed reviewed contract #{row['declaration']}: #{p}" unless h==reviewed.fetch(p) && h==record.fetch('input_hashes').fetch(p)
        end
        config=JSON.parse(rendered.fetch(row['configuration']))
        raise 'Contract target mismatch' unless config.fetch('theorem_names').sort==record.fetch('targets').sort
        raise 'Definition holes are not permitted' unless config.fetch('definition_names')==[]
        raise 'Unapproved axioms' unless config.fetch('permitted_axioms').sort==AXIOMS.sort
        raise 'Reference module mismatch' unless config.fetch('challenge_module')+'.lean'==row['reference_file']
        raise 'Solution module mismatch' unless config.fetch('solution_module')+'.lean'==row['solution_file']
        reference=rendered.fetch(row['reference_file'])
        if row['scope']!='comparison'
          imports=reference.lines.grep(/^\s*(?:public\s+)?import\s+/)
          raise 'Existence/discriminator reference is not mathlib-only' if imports.empty? || !imports.all? { |l|l.strip.start_with?('import Mathlib.') }
        end
        solution=rendered.fetch(row['solution_file'])
        raise 'Unproved solution' if solution.match?(/\b(?:sorry|admit|axiom|native_decide)\b/)
        raise 'Solution imports reference' if solution.match?(/^\s*import\s+(?:Challenge|Reference)\b/)
        raise 'Contract inputs changed during run' unless record.fetch('inputs_unchanged')
        if record['status']=='passed'
          stage=record.fetch('stage')
          raise 'Unsuccessful process marked passed' unless stage['status']=='process-passed' && stage['exit_code']==0 && stage['signal'].nil? && stage['guard_stop'].nil?
          unless seen[evidence]
            digest=Digest::SHA256.new;markers={kernel:false,accepted:false};tail=''
            g=Zlib::GzipReader.new(StringIO.new(read(evidence+'/comparator-check.log.gz')))
            until g.eof?
              chunk=g.read(1024*1024);digest.update(chunk);text=tail+chunk
              markers[:kernel] ||= text.include?('Lean default kernel accepts the solution')
              markers[:accepted] ||= text.include?('Your solution is okay!')
              tail=text[-120,120] || text
            end
            g.close
            raise 'Original Comparator log changed' unless digest.hexdigest==stage.fetch('log_sha256')
            raise 'Missing actual Comparator acceptance markers' unless markers.values.all?
            seen[evidence]=true
          end
        else
          raise 'Unexpected failed target' unless record['status']=='incomplete' && DEFERRED.include?(row['declaration']) && record.dig('stage','guard_stop')
        end
        row.merge('recorded_status'=>record['status'],'recorded_date'=>record.fetch('finished_utc'),
          'current_export_acceptance'=>'not inferred from historical receipt')
      end
      open=results.reject { |r|r['recorded_status']=='passed' }.map { |r|r['declaration'] }.sort
      raise 'Deferred outcomes changed unexpectedly' unless open==DEFERRED
      raise 'Recorded target count changed' unless original['target_count']==45 && original['passed_targets']==42 && bundle['targets']==45 && bundle['passed']==42
      {entries:results,passed:42,total:45,open:open,models:39,primary_models:33,
        bundle:directory,source_hashes:directory+'/SOURCE_HASHES.json'}
    end
  end
  def self.entries = Index.new.entries
  def self.render(row)=Index.new.render(row)
end
