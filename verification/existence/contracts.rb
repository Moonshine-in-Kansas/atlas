# Shared rendering of reviewed contracts. Never infer mathematical specifications from proofs.
require 'json'
module AtlasContracts
  ROOT = File.expand_path('../..', __dir__)
  SCOPES = {'existence'=>['verification/existence','AtlasExistence'],
            'discriminators'=>['verification/existence/discriminators','AtlasDistinguished']}.freeze
  AXIOMS = %w[propext Quot.sound Classical.choice].freeze
  def self.entries
    rows=JSON.parse(File.read(ROOT+'/verification/existence/registry.json')).fetch('entries')
    raise 'Duplicate declaration' unless rows.map{|r|r.fetch('declaration')}.uniq.size==rows.size
    rows.each do |r|
      _, ns=SCOPES.fetch(r.fetch('scope'))
      raise 'Invalid target name' unless r.fetch('declaration').match?(/\A#{ns}\.\w+\z/)
      raise 'Invalid imports' unless r.fetch('imports').all?{|s|s.match?(/\AAtlas(?:\.\w+)+\z/)}
      raise 'Unsafe evidence path' unless r.fetch('evidence').match?(%r{\Averification/existence/(?:discriminators/)?[\w-]+/\w+\z})
    end
    rows
  end
  def self.config(names)
    {'challenge_module'=>'Challenge','solution_module'=>'Solution','theorem_names'=>names,
     'definition_names'=>[],'permitted_axioms'=>AXIOMS}
  end
  def self.render(row)
    path,ns=SCOPES.fetch(row.fetch('scope'))
    expected=entries.select{|r|r['scope']==row['scope']}.map{|r|r['declaration']}.sort
    files=%w[Challenge Solution].to_h do |side|
      text=File.read(ROOT+"/#{path}/#{side}.lean")
      blocks=text.split(/(?=^theorem #{ns}\.)/)
      names=blocks.drop(1).map{|b|b[/^theorem (\S+)/,1]}
      raise "Registry/contract mismatch: #{path}/#{side}" unless names.sort==expected
      header=blocks.first
      if side=='Challenge'
        raise 'Reference must import only mathlib' unless header.lines.grep(/^import /).all?{|l|l.start_with?('import Mathlib.')}
      else
        raise 'Unproved solution' if text.match?(/\b(sorry|admit|axiom|native_decide)\b/)
        raise 'Solution imports reference' if text.match?(/^import .*Challenge/)
        imports=row.fetch('imports').map{|s|"import #{s}\n"}.join
        if row['scope']=='existence'
          raise 'Missing combined Atlas import' unless header.include?("import Atlas\n")
          header=header.sub("import Atlas\n",imports)
        else
          header=imports+header.lines.reject{|l|l.start_with?('import Atlas.')}.join
        end
      end
      body=blocks.drop(1).find{|b|b.start_with?("theorem #{row.fetch('declaration')} ")}
      raise 'Missing theorem body' unless body
      [side+'.lean',header+body]
    end
    files['comparator.json']=JSON.pretty_generate(config([row.fetch('declaration')]))+"\n"
    files
  end
end
