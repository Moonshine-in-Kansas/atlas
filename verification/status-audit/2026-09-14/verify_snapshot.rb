require 'json';require 'digest';require 'open3'
d=__dir__;s=JSON.parse(File.read("#{d}/SNAPSHOT.json"))
s['sources'].each{|p,j|abort "Changed source #{p}" unless Digest::SHA256.file(p).hexdigest==j['sha256']}
s['pins'].each{|p,h|abort "Changed pin #{p}" unless Digest::SHA256.file(p).hexdigest==h}
s['dependency_checkouts'].each{|p,h|x,st=Open3.capture2('git','-C',p,'rev-parse','HEAD');abort "Changed dependency #{p}" unless st.success?&&x.strip==h}
abort 'Tracked proof changes' unless system('git','diff','--exit-code',s['commit'],'--','Atlas.lean','Atlas','lean-toolchain','lakefile.toml','lake-manifest.json',out:File::NULL)
s['dependency_checkouts'].each_key{|p|x,st=Open3.capture2('git','-C',p,'status','--porcelain=v1','--untracked-files=no');abort "Dirty dependency #{p}" unless st.success? && x.empty?}
puts 'All audited Atlas sources, tracked proofs, pins and dependency revisions unchanged.'
