# Stage versioned diagrams while preserving Version 1.0's existing URLs.
require 'json'
require 'digest'
require 'fileutils'
require 'cgi'
require 'open3'
require_relative '../../catalogue/model_views'
ROOT=File.expand_path('../..',__dir__)
Dir.chdir(ROOT)
out=File.expand_path(ARGV.fetch(0) { abort 'Usage: ruby verification/dependency-maps/build_site.rb EMPTY_OUTPUT_DIRECTORY' })
abort 'Output must be new or empty' if File.exist?(out) && (!File.directory?(out) || !Dir.empty?(out))
old_git=ENV.fetch('ATLAS_V1_GIT_DIR',ROOT+'/.git')
old_ref=ENV.fetch('ATLAS_V1_REF','v1.0')
expected='3c4e29f12a48132ee9ce7b11e01eb1dff766331e'
def git_read(git_dir,ref,path)
  s,st=Open3.capture2('git','--git-dir='+git_dir,'show',ref+':'+path)
  raise "Cannot read preserved #{path}" unless st.success?
  s
end
commit,st=Open3.capture2('git','--git-dir='+old_git,'rev-parse',old_ref+'^{commit}')
raise 'Preserved Version 1.0 changed' unless st.success? && commit.strip==expected
current_ref=ENV['ATLAS_SITE_CURRENT_REF'] || Open3.capture2('git','rev-parse','HEAD').first.strip
raise 'Unsafe source reference' unless current_ref.match?(/\A(?:[0-9a-f]{40}|v1\.2|v1\.2-review)\z/)
current=JSON.parse(File.read('catalogue/catalogue.json'))
old=JSON.parse(git_read(old_git,old_ref,'catalogue/catalogue.json'))
model_views=AtlasModelViews::View.new(ROOT)
def write(out,p,s)
  target=File.join(out,p);FileUtils.mkdir_p(File.dirname(target));File.write(target,s)
end
def index(entries,prefix,version,ref,models=nil)
  links=entries.map do |e|
    title=e.dig('presentation','label')||e.fetch('label')
    extra=''
    if models
      base="https://github.com/Moonshine-in-Kansas/atlas/blob/#{ref}/"
      links=models.models.fetch(e['id']).map { |m|%(<a href="#{base}CATALOGUE.md##{models.model_anchor(m)}">#{CGI.escapeHTML(m['label'])}</a>) }
      certs=models.edges(e['id']).map { |c|%(<a href="#{base}catalogue/ISOMORPHISMS.md##{c['id']}">Lean isomorphism certificate</a>) }
      extra="<br><small>"+(links+certs).join(' · ')+'</small>'
    end
    %(<li><a href="#{prefix}#{e.fetch('proof_dependencies')}">#{CGI.escapeHTML(title)}</a>#{extra}</li>)
  end.join
  <<~HTML
    <!doctype html><html lang="en"><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
    <title>ATLAS #{version} proof dependencies</title><style>body{font:18px system-ui;max-width:750px;margin:3rem auto;padding:1rem;line-height:1.7;color:#243b56}a{color:#2465a6}</style>
    <h1>ATLAS #{version} proof dependencies</h1><p>Interactive graphs, trees and theorem counts.</p><ul>#{links}</ul>
    <p><a href="https://github.com/Moonshine-in-Kansas/atlas/blob/#{ref}/CATALOGUE.md">Source catalogue</a></p></html>
  HTML
end
versions=[['v1.0',old,old_ref],['v1.2',current,current_ref]]
versions.each do |version,registry,ref|
  entries=registry.fetch('entries').select { |e|e['proof_dependencies'] }
  entries.each do |e|
    p=e.fetch('proof_dependencies')
    raise 'Unsafe diagram path' unless p.match?(%r{\Averification/dependency-maps/[a-z0-9]+/[A-Za-z0-9]+\.html\z})
    html=version=='v1.0' ? git_read(old_git,old_ref,p) : File.read(p)
    data=JSON.parse(html[/<script id="data" type="application\/json">(.*?)<\/script>/m,1])
    raise 'Wrong order root' unless data.dig('roots','order')==e.dig('roles','order','declaration')
    data.fetch('source_hashes').each do |src,h|
      bytes=version=='v1.0' ? git_read(old_git,old_ref,src) : File.binread(src)
      raise "Changed #{version} source #{src}" unless Digest::SHA256.hexdigest(bytes)==h
    end
    html=html.gsub("'../../../'", "'https://github.com/Moonshine-in-Kansas/atlas/blob/#{ref}/'")
    html=html.gsub('href="../../../','href="https://github.com/Moonshine-in-Kansas/atlas/blob/'+ref+'/') if version=='v1.2'
    write(out,version+'/'+p,html)
    # Existing external links keep serving the exact previous diagrams and sources.
    write(out,p,html) if version=='v1.0'
  end
  write(out,version+'/index.html',index(entries,'',version,ref,version=='v1.2' ? model_views : nil))
end
home=index(current.fetch('entries'),'v1.2/','v1.2',current_ref,model_views)
home.sub!('</h1>', '</h1><p><a href="v1.0/">Preserved Version 1.0 diagrams</a> · <a href="https://github.com/Moonshine-in-Kansas/atlas/releases/tag/v1.0">Immutable Version 1.0 release</a></p>')
write(out,'index.html',home)
write(out,'.nojekyll','')
puts "PASS: staged #{current.fetch('entries').size} Version 1.2 and #{old.fetch('entries').size} preserved Version 1.0 diagrams; legacy URLs retained. No deployment performed."
