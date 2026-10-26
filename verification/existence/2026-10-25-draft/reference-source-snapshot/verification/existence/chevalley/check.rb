require 'json'
require 'digest'

module ChevalleyContracts
  BASE = __dir__
  ROOT = File.expand_path('../../..', BASE)
  AXIOMS = %w[propext Quot.sound Classical.choice].freeze
  KEYS = %w[A B C D E6 E7 E8 F4 G2].freeze

  def self.entries
    JSON.parse(File.read(BASE+'/registry.json')).fetch('entries')
  end

  def self.check
    rows = entries
    raise 'Unexpected target inventory' unless rows.map { |r| r.fetch('key') } == KEYS
    raise 'Duplicate declaration' unless rows.map { |r| r.fetch('declaration') }.uniq.size == rows.size
    rows.each do |row|
      key = row.fetch('key')
      decl = "AtlasExistenceChevalley.#{key}"
      raise 'Wrong target name' unless row.fetch('declaration') == decl
      dir = BASE+'/'+key
      ref, sol = %w[Challenge Solution].map { |side| File.read(dir+"/#{side}.lean") }
      statement = ->(text) { text.split(/^theorem /, 2).fetch(1).split(':= by', 2).first.strip }
      raise "Statement mismatch: #{key}" unless statement.call(ref) == statement.call(sol)
      raise "Extra theorem: #{key}" unless [ref, sol].all? { |s| s.scan(/^theorem /).size == 1 }
      raise "Unclean reference: #{key}" unless ref.lines.grep(/^import /).all? { |l| l.start_with?('import Mathlib.') }
      raise "Unexpected reference hole: #{key}" unless ref.scan(/\bsorry\b/).size == 1 && !ref.match?(/\b(axiom|admit)\b/)
      raise "Unproved solution: #{key}" if sol.match?(/\b(sorry|admit|axiom|native_decide)\b/)
      raise "Unexpected imports: #{key}" unless sol.lines.grep(/^import /).map { |s| s.split.last } == row.fetch('imports')
      raise "Wrong witness: #{key}" unless sol.include?("⟨#{row.fetch('carrier')}, inferInstance, inferInstance,")
      raise "Wrong order proof: #{key}" unless sol.include?(row.fetch('order_declaration'))
      raise "Wrong simplicity proof: #{key}" unless sol.include?(row.fetch('simplicity_declaration'))
      raise "Incomplete contract: #{key}" unless statement.call(sol).include?('Nat.card G =') && statement.call(sol).include?('IsSimpleGroup G')
      cfg = JSON.parse(File.read(dir+'/comparator.json'))
      expected = {'challenge_module'=>'Challenge', 'solution_module'=>'Solution',
        'theorem_names'=>[decl], 'definition_names'=>[], 'permitted_axioms'=>AXIOMS}
      raise "Wrong Comparator configuration: #{key}" unless cfg == expected
      row.fetch('imports').each do |mod|
        raise "Missing imported source: #{mod}" unless File.file?(ROOT+'/'+mod.tr('.', '/')+'.lean')
      end
    end
    rows
  end
end

if $PROGRAM_NAME == __FILE__
  puts "PASS: #{ChevalleyContracts.check.size} matched references and concrete Chevalley solutions; independent configurations."
end
