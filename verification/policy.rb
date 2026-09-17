require 'set'
module AtlasVerification
  AXIOMS=%w[propext Classical.choice Quot.sound].freeze
  FORBIDDEN=%w[sorryAx native_decide ofReduceBool ofReduceNat].freeze
  def self.closure(nodes, roots)
    seen=Set.new; work=roots.dup
    until work.empty?
      name=work.pop; next unless seen.add?(name)
      raise "Missing dependency node #{name}" unless nodes.key?(name)
      work.concat(nodes[name].fetch('dependencies'))
    end
    seen
  end
  def self.check_policy(manifest, records, nodes)
    allowed=manifest.fetch('allowed_axioms',AXIOMS)
    raise 'Cannot extend trusted axioms' unless (allowed-AXIOMS).empty?
    records.each{|r|raise "Unapproved axiom in #{r['declaration']}" unless (r.fetch('axioms')-allowed).empty?}
    rules=manifest.fetch('boundaries',[])
    raise 'Boundary checks require full mode' if nodes.nil? && !rules.empty?
    return [] unless nodes
    visited=closure(nodes,records.map{|r|r['declaration']})
    raise 'Extraneous graph nodes' unless visited.size==nodes.size
    visited.each do |n|
      raise "Forbidden dependency #{n}" if FORBIDDEN.any?{|s|n.include?(s)}
      raise "Unapproved axiom #{n}" if nodes[n]['kind']=='axiom'&&!allowed.include?(n)
    end
    results=[]
    rules.each do |rule|
      unknown=rule.keys-%w[id roots root_prefixes all_roots forbid_name_prefixes forbid_modules module_allowlists]
      raise "Unknown boundary fields #{unknown}" unless unknown.empty?
      rule.fetch('module_allowlists',[]).each do |g|
        raise 'Unknown allowlist field' unless (g.keys-%w[prefix modules]).empty?
      end
      selected=records.map{|r|r['declaration']}.select do |n|
        rule.fetch('roots',[]).include?(n)||rule.fetch('root_prefixes',[]).any?{|p|n.start_with?(p)}||rule['all_roots']==true
      end
      raise "Vacuous boundary #{rule['id']}" if selected.empty?
      closure(nodes,selected).each do |n|
        mod=nodes[n]['module']
        raise "Boundary #{rule['id']}: forbidden #{n}" if rule.fetch('forbid_name_prefixes',[]).any?{|p|n.start_with?(p)} || rule.fetch('forbid_modules',[]).include?(mod)
        rule.fetch('module_allowlists',[]).each do |gate|
          if mod.start_with?(gate.fetch('prefix'))&&!gate.fetch('modules').include?(mod)
            raise "Boundary #{rule['id']}: outside module #{mod} at #{n}"
          end
        end
      end
      results<<{id:rule['id'],roots:selected.size,status:'passed'}
    end
    results
  end
end
