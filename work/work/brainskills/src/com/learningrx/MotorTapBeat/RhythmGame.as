package com.learningrx.MotorTapBeat {

import flash.display.MovieClip;
	
public class RhythmGame	extends MovieClip {
	
	protected var m_metronome:Metronome;
	protected var m_game:MotorTapBeat;
	
	private var m_tried:Boolean = false;
	private var m_tryOffset:Number = 0;
	
	function RhythmGame(game:MotorTapBeat) {
		m_game = game;
	}
	
	public function begin():void {
		addEventListener('enterFrame', step);
		m_metronome = makeMetronome();
		m_metronome.begin();
		m_lastGuess = true;
	}
	
	public function end():void {
		m_metronome.end();
		removeEventListener('enterFrame', step);
	}
	
	protected function makeMetronome():Metronome {
		throw new Error("Abstract method make_metronome() called");
	}
	
	protected function onHit(beatIndex:int, dir:String):void {
		throw new Error("Abstract method onHit() called");
	}
	
	protected function onMissHit(beatIndex:int, dir:String):void {
		throw new Error("Abstract method onMissHit() called");
	}
	
	protected function onMiss(beatIndex:int):void {
		throw new Error("Abstract method onMiss() called");
	}
	
	protected function beatCounts(beatIndex:int):Boolean {
		throw new Error("Abstract method beatCounts() called");
	}
	
	protected function step(e = null):void {
		var beat:Object = m_metronome.nearestBeat();
		
		// missed the mark

		if (beatCounts(beat.index) && m_tryOffset < 100 && beat.offset >= 100) {
			if (!m_tried) {
				onMiss(beat.index);
			}
			m_tried = false;
			m_tryOffset = beat.offset;
		}
		m_tryOffset = beat.offset;
	}

	public function OnArrowKeyPressed(dir:String):void {		
		var beat:Object;
		beat = m_metronome.nearestBeat();
		
		if (m_tried) { return; }
		m_tried = true;

		if (beat.offset < 100 && beatCounts(beat.index)) {  // XXX magic number, tolerance
			onHit(beat.index, dir);
		}
		else {
			onMissHit(beat.index, dir);
		}
	}
}

}
