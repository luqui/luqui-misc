package com.learningrx.MotorTapBeat {
	
import flash.media.Sound;
import flash.utils.getDefinitionByName;

public class RhythmGameToneHearing extends RhythmGame {
	
	private var m_tones:Array;
	private var m_toneQueue:Array;
	private var m_interval:Number;
	
	function RhythmGameToneHearing(game:MotorTapBeat, interval:Number) {
		super(game);
		m_interval = interval;
		
		m_tones = [];
		for each (var i:String in ["C3", "G3", "C4", "G4", "C5", "G5"]) {
			var prefix:String = "com.learningrx.MotorTapBeat.Tone" + i;
			var tone = {
				short: new (getDefinitionByName(prefix + "Short") as Class)(),
				norm:  new (getDefinitionByName(prefix + "Norm") as Class)(),
				long:  new (getDefinitionByName(prefix + "Long") as Class)()
			};
			m_tones.push(tone);
		}
		m_toneQueue = [];
	}
	
	protected override function makeMetronome():Metronome {
		var met = new Metronome(m_interval);
		var self = this;
		met.setFireCallback(function (count) {
			var toneIdx:int;
			do {
				// pick a tone, make sure it is not the same as the previous one
				toneIdx = int(self.m_tones.length * Math.random());
			} while (self.m_toneQueue.length > 0 && self.m_toneQueue[self.m_toneQueue.length-1] == toneIdx);
			// play that tone
			m_tones[toneIdx].norm.play();
			// and record it in the list
			m_toneQueue.push(toneIdx);
		});
		return met;
	}
	
	protected override function beatCounts(beatIdx:int):Boolean {
		return beatIdx > 2;
	}
	
	protected override function onHit(beatIndex:int, dir:String):void {
		if (m_toneQueue[1] > m_toneQueue[0] && dir == "up" ||
			m_toneQueue[1] < m_toneQueue[0] && dir == "down") {
				m_game.ScoreRight();
		}
		m_toneQueue.shift();
	}
	
	protected override function onMissHit(beatIndex:int, dir:String):void {
		m_game.ScoreWrong();
		m_toneQueue.shift();
	}
	
	protected override function onMiss(beatIndex:int):void {
		m_game.ScoreWrong();
		m_toneQueue.shift();
	}
}

}