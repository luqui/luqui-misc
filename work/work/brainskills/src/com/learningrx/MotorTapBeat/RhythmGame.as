package com.learningrx.MotorTapBeat {

import flash.display.MovieClip;
	
public class RhythmGame	extends MovieClip {
	
	protected var m_metronome:Metronome;
	
	public function begin():void {
		addEventListener('keyDown', keyDown);
		addEventListener('enterFrame', step);
		m_metronome = makeMetronome();
		m_metronome.begin();
	}
	
	public function end():void {
		m_metronome.end();
		removeEventListener('enterFrame', step);
		removeEventListener('keyDown', keyDown);
	}
	
	protected function makeMetronome():Metronome {
		throw new Error("Abstract method make_metronome() called");
	}
	
	protected function onHit(beatIndex:int, keyCode:int):void {
		throw new Error("Abstract method onHit() called");
	}
	
	protected function onMiss(beatIndex:int, keyCode:int):void {
		throw new Error("Abstract method onMiss() called");
	}
	
	protected function step(e = null):void { }
	
	private function keyDown(e):void {
		var beat:Object;
		beat = m_metronome.nearestBeat();
		if (beat.offset < 100) {  // XXX magic number, tolerance
			onHit(beat.index, e.keyCode);
		}
		else {
			onMiss(beat.index, e.keyCode);
		}
	}
}

}
