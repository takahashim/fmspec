# frozen_string_literal: true

require_relative "../lib/fmspec/version"

Gem::Specification.new do |spec|
  spec.name = "fmspec-rails"
  spec.version = Fmspec::VERSION
  spec.authors = ["takahashim"]
  spec.summary = "Model-based testing of Rails applications with fmspec"
  spec.description = "Isolation, Active Job, request and time helpers for binding fmspec " \
                     "specifications to a Rails application."
  spec.required_ruby_version = ">= 3.3"
  spec.files = Dir["lib/**/*.rb", "README.md"]
  spec.require_paths = ["lib"]

  spec.add_dependency "actionpack", ">= 7.1"
  spec.add_dependency "activejob", ">= 7.1"
  spec.add_dependency "activerecord", ">= 7.1"
  spec.add_dependency "fmspec", Fmspec::VERSION
end
