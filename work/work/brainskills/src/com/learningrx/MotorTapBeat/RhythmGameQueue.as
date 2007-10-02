package com.learningrx.MotorTapBeat {

public class RhythmGameQueue extends RhythmGame
{
	protected var m_queue:Array;
	protected var m_interval:Number;
	
	function RhythmGameQueue(game:MotorTapBeat, interval:Number) {
		super(game);
		m_interval = interval;
		m_queue = [];
	}
	
	protected override function makeMetronome():Metronome {
		var met = new Metronome(m_interval);
		var self = this;
		met.setFireCallback(function (count) {
			var idx = pickIndex(self.m_queue[self.m_queue.length-1]);
			playIndex(idx);
			m_queue.push(idx);
		});
		return met;
	}
	
	protected function pickIndex(prev:Object):Object {
		throw new Error("Call abstract method pickIndex()");
	}
	
	protected function playIndex(index:Object):void {
		throw new Error("Call abstract method playIndex()");
	}
	
	protected override function beatCounts(beat:int):Boolean {
		return beat >= 2;
	}
	
	protected function subOnHit(beat:int, prev2:Object, prev1:Object, dir:String):Boolean {
		throw new Error("Call abstract method subOnHit()");
	}
	
	protected override function onHit(beatIndex:int, dir:String):void {
		if (subOnHit(beatIndex, m_queue[0], m_queue[1], dir)) {
			m_game.ScoreRight();
		}
		else {
			m_game.ScoreWrong();
		}
		m_queue.shift();
	}
	
	protected override function onMissHit(beatIndex:int, dir:String):void {
		m_game.ScoreWrong();
		m_queue.shift();
	}
	
	protected override function onMiss(beatIndex:int):void {
		m_game.ScoreWrong();
		m_queue.shift();
	}
}

}