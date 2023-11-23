use clap::Parser;
use comune::cli::ComuneCLI;

fn main() -> color_eyre::eyre::Result<()> {
	color_eyre::install()?;

	if comune::cli::run(ComuneCLI::parse()).is_err() {
		std::process::exit(1);
	};

	Ok(())
}
