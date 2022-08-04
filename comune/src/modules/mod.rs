use std::{ffi::OsString, sync::{Barrier, Arc}};
use threadpool::ThreadPool;

pub struct ModuleJobManager {
	import_paths: Vec<OsString>,
	working_dir: OsString,
	thread_pool: ThreadPool,
	job_queue: Vec<OsString>,
	barrier: Arc<Barrier>,
}

impl ModuleJobManager {
	pub fn new(working_dir: OsString, import_paths: Vec<OsString>, max_threads: usize) -> Self {
		ModuleJobManager { 
			import_paths, 
			working_dir, 
			thread_pool: ThreadPool::new(max_threads), 
			job_queue: vec![],
			barrier: Arc::new(Barrier::new(max_threads)),
		}
	}

	fn add_job(&mut self, path: OsString) {
		self.job_queue.push(path);
	}

	fn wait(&self) {
		self.barrier.wait();
	}
}