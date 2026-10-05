# Stage only the catalogue-linked diagrams for GitHub Pages; never enable or deploy Pages.
require 'json'
require 'digest'
require 'fileutils'
require 'cgi'
root=File.expand_path('../..',__dir__)
Dir.chdir(root)
out=ARGV.fetch(0) { abort 'Usage: ruby verification/dependency-maps/build_site.rb EMPTY_OUTPUT_DIRECTORY' }
abort 'Output must be a new/empty directory' if File.exist?(out)&&(!File.directory?(out)||!Dir.empty?(out))
catalogue=JSON.parse(File.read('catalogue/catalogue.json'))
entries=catalogue.fetch('entries').select{|e|e['proof_dependencies']}
abort 'No diagrams in catalogue' if entries.empty?
links=[]
entries.each do |entry|
 path=entry.fetch('proof_dependencies')
 raise 'Unsafe path' unless path.match?(%r{\Averification/dependency-maps/[a-z][a-z0-9]*/[A-Z][A-Za-z0-9]*\.html\z})
 text=File.read(path)
 data=JSON.parse(text[/<script id="data" type="application\/json">(.*?)<\/script>/m,1])
 raise 'Wrong order root' unless data.dig('roots','order')==entry.dig('roles','order','declaration')
 raise 'Wrong simplicity root' unless ([entry.dig('roles','simple','declaration')]+entry.fetch('properties',[]).map{|p|p['declaration']}).include?(data.dig('roots','simplicity'))
 data.fetch('source_hashes').each{|p,h|raise "Stale source #{p}" unless Digest::SHA256.file(p).hexdigest==h}
 # Keep cross-group links relative; source/audit links should open GitHub, not missing website files.
 text=text.gsub("'../../../'", "'https://github.com/Moonshine-in-Kansas/atlas/blob/main/'")
 target=File.join(out,path);FileUtils.mkdir_p(File.dirname(target));File.write(target,text)
 label=entry.dig('presentation','label')||entry.fetch('label')
 links<<"<li><a href=\"#{path}\">#{CGI.escapeHTML(label)}</a></li>"
end
File.write(File.join(out,'index.html'),<<~HTML)
<!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1"><title>ATLAS proof dependencies</title><style>body{font:18px system-ui;max-width:750px;margin:3rem auto;padding:1rem;line-height:1.7;color:#243b56}a{color:#2465a6}</style><h1>ATLAS proof dependencies</h1><p>Interactive graphs, trees and theorem counts.</p><ul>#{links.join}</ul><p><a href="https://github.com/Moonshine-in-Kansas/atlas/blob/main/CATALOGUE.md">Return to the catalogue</a></p></html>
HTML
File.write(File.join(out,'.nojekyll'),'')
puts "Staged #{entries.size} source-checked diagrams in #{out}. No site has been enabled or deployed."
