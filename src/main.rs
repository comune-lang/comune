use clap::Parser;
use comune::cli::ComuneCLI;

fn main() -> color_eyre::eyre::Result<()> {
	color_eyre::install()?;

	comune::cli::run(ComuneCLI::parse());
	
	Ok(())
}
