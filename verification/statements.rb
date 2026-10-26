# Compatibility entry point; one renderer owns all generated catalogue pages.
mode=ARGV.fetch(0,'check')
abort 'Usage: statements.rb [refresh|check]' unless %w[refresh check].include?(mode)
exec('ruby',File.expand_path('../catalogue/manage.rb',__dir__),mode)
